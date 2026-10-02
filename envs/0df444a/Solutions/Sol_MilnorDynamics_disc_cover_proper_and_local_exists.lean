-- Prove2me | solution 1 for MilnorDynamics.disc_cover_proper_and_local_exists
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:56:17.446828+00:00
-- url     : https://prove2.me/submissions/e7f89fcb-d205-46ba-87e2-42dd35395c64

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

section Helpers3efd

/-- Key refutation: no complex-differentiable map of the unit disc into `{0,1}ᶜ` with image
`{0,1}ᶜ` is proper onto `{0,1}ᶜ` (maximum modulus on a circle avoiding `|p| = 2`). -/
theorem no_proper_disc_map_3efd (p : ℂ → ℂ) (hd : DifferentiableOn ℂ p (Metric.ball 0 1))
    (hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))
    (him : p '' (Metric.ball 0 1) = {0, 1}ᶜ)
    (hprop : IsProperMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))) : False := by
  set f := hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) with hf
  -- the circle |w| = 2 inside {0,1}ᶜ
  have hsub : Metric.sphere (0 : ℂ) 2 ⊆ ({0, 1}ᶜ : Set ℂ) := by
    intro w hw
    simp only [mem_sphere_iff_norm, sub_zero] at hw
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · rintro rfl; norm_num at hw
    · rintro rfl; norm_num at hw
  set K : Set ({0, 1}ᶜ : Set ℂ) := Subtype.val ⁻¹' Metric.sphere (0 : ℂ) 2 with hK
  have hKc : IsCompact K := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr hsub]
    exact isCompact_sphere 0 2
  have hpre : IsCompact (f ⁻¹' K) := hprop.isCompact_preimage hKc
  set C : Set ℂ := Subtype.val '' (f ⁻¹' K) with hC
  have hCc : IsCompact C := hpre.image continuous_subtype_val
  have hCsub : C ⊆ Metric.ball 0 1 := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  obtain ⟨r, hr1, hCr⟩ := exists_lt_subset_ball hCc.isClosed hCsub
  have hkey : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖p z‖ = 2 → ‖z‖ < r := by
    intro z hz h2
    have : z ∈ C := ⟨⟨z, hz⟩, by
      show (f ⟨z, hz⟩ : ℂ) ∈ Metric.sphere (0 : ℂ) 2
      simp [hf, MapsTo.val_restrict_apply, h2], rfl⟩
    have := hCr this
    simpa using this
  -- points with values 1/2 and 3
  have h12 : (1 / 2 : ℂ) ∈ ({0, 1}ᶜ : Set ℂ) := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; norm_num
  have h3 : (3 : ℂ) ∈ ({0, 1}ᶜ : Set ℂ) := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; norm_num
  rw [← him] at h12 h3
  obtain ⟨z1, hz1, hpz1⟩ := h12
  obtain ⟨z2, hz2, hpz2⟩ := h3
  have hz1' : ‖z1‖ < 1 := by simpa using hz1
  have hz2' : ‖z2‖ < 1 := by simpa using hz2
  set s : ℝ := (max (max r ‖z1‖) ‖z2‖ + 1) / 2 with hs
  have hm1 : max (max r ‖z1‖) ‖z2‖ < 1 := max_lt (max_lt hr1 hz1') hz2'
  have hrs : r < s := by
    have : r ≤ max (max r ‖z1‖) ‖z2‖ := le_trans (le_max_left _ _) (le_max_left _ _)
    rw [hs]; linarith
  have hz1s : ‖z1‖ < s := by
    have : ‖z1‖ ≤ max (max r ‖z1‖) ‖z2‖ := le_trans (le_max_right _ _) (le_max_left _ _)
    rw [hs]; linarith
  have hz2s : ‖z2‖ < s := by
    have : ‖z2‖ ≤ max (max r ‖z1‖) ‖z2‖ := le_max_right _ _
    rw [hs]; linarith
  have hs1 : s < 1 := by rw [hs]; linarith
  have hs0 : 0 < s := lt_of_le_of_lt (norm_nonneg _) hz1s
  have hcl : closure (Metric.ball (0 : ℂ) s) = Metric.closedBall 0 s :=
    closure_ball 0 hs0.ne'
  have hfr : frontier (Metric.ball (0 : ℂ) s) = Metric.sphere 0 s :=
    frontier_ball 0 hs0.ne'
  have hcb : Metric.closedBall (0 : ℂ) s ⊆ Metric.ball 0 1 := Metric.closedBall_subset_ball hs1
  have hdc : DiffContOnCl ℂ p (Metric.ball (0 : ℂ) s) := by
    apply DifferentiableOn.diffContOnCl
    rw [hcl]; exact hd.mono hcb
  have hne0 : ∀ z ∈ Metric.ball (0 : ℂ) 1, p z ≠ 0 := by
    intro z hz h0
    have := hp hz
    rw [h0] at this
    simp at this
  have hsph1 : Metric.sphere (0 : ℂ) s ⊆ Metric.ball 0 1 :=
    Metric.sphere_subset_closedBall.trans hcb
  have hnot2 : ∀ z ∈ Metric.sphere (0 : ℂ) s, ‖p z‖ ≠ 2 := by
    intro z hz h2
    have := hkey z (hsph1 hz) h2
    have hzs : ‖z‖ = s := by simpa using hz
    linarith
  have hz1cl : z1 ∈ closure (Metric.ball (0 : ℂ) s) := by
    rw [hcl]; simpa using hz1s.le
  have hz2cl : z2 ∈ closure (Metric.ball (0 : ℂ) s) := by
    rw [hcl]; simpa using hz2s.le
  by_cases hall : ∀ z ∈ Metric.sphere (0 : ℂ) s, ‖p z‖ ≤ 2
  · have := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc
      (by rw [hfr]; exact hall) hz2cl
    rw [hpz2] at this
    norm_num at this
  · push Not at hall
    obtain ⟨a, ha, hpa⟩ := hall
    have hconn : IsPreconnected (Metric.sphere (0 : ℂ) s) :=
      (isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 hs0.le).isPreconnected
    have hcont : ContinuousOn (fun z => ‖p z‖) (Metric.sphere (0 : ℂ) s) :=
      (hd.continuousOn.mono hsph1).norm
    have hgt : ∀ z ∈ Metric.sphere (0 : ℂ) s, 2 ≤ ‖p z‖ := by
      intro b hb
      by_contra hlt
      push Not at hlt
      obtain ⟨c, hc, hc2⟩ := hconn.intermediate_value hb ha hcont
        (show (2 : ℝ) ∈ Icc ‖p b‖ ‖p a‖ from ⟨hlt.le, hpa.le⟩)
      exact hnot2 c hc hc2
    have hdc' : DiffContOnCl ℂ (fun z => (p z)⁻¹) (Metric.ball (0 : ℂ) s) := by
      apply DifferentiableOn.diffContOnCl
      rw [hcl]
      exact (hd.mono hcb).inv (fun z hz => hne0 z (hcb hz))
    have := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc'
      (C := 1 / 2) (by
        rw [hfr]
        intro z hz
        have h2 := hgt z hz
        rw [norm_inv]
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        norm_num; exact h2) hz1cl
    simp only [hpz1] at this
    norm_num at this

end Helpers3efd

theorem solution : ¬ (exists p : ℂ -> ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) /\
      exists hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        p '' (Metric.ball 0 1) = {0, 1}ᶜ /\
          IsProperMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) /\
            IsLocalHomeomorph
              (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))) := by
  rintro ⟨p, hd, hp, him, hprop, -⟩
  exact no_proper_disc_map_3efd p hd hp him hprop
