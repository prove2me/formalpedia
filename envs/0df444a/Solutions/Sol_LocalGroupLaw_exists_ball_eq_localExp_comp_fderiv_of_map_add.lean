-- Prove2me | solution 1 for LocalGroupLaw.exists_ball_eq_localExp_comp_fderiv_of_map_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d2ea8086-4086-5843-8aab-141f252e1fbe

import Mathlib
import Theorems.Thm_Complex_contDiffOn_infty_of_differentiableOn_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGroupLaw_exists_ball_eq_localExp_comp_fderiv_of_map_add

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Topology Filter Metric Set

noncomputable section

namespace LocalGroupLawB2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem eq_of_additive_of_hasFDerivAt {k : E → E} {A : E →L[ℂ] E} {s : ℝ} (hs : 0 < s)
    (hk0 : k 0 = 0)
    (hadd : ∀ v w : E, v ∈ ball (0 : E) s → w ∈ ball (0 : E) s → v + w ∈ ball (0 : E) s →
      k (v + w) = k v + k w)
    (hA : HasFDerivAt k A 0) {v : E} (hv : v ∈ ball (0 : E) s) : k v = A v := by

  have hhalf_mem : ∀ m : ℕ, ((2 : ℂ)⁻¹ ^ m) • v ∈ ball (0 : E) s := by
    intro m
    rw [mem_ball_zero_iff] at hv ⊢
    calc ‖((2 : ℂ)⁻¹ ^ m) • v‖ = ‖(2 : ℂ)⁻¹ ^ m‖ * ‖v‖ := norm_smul _ _
      _ ≤ 1 * ‖v‖ := by
          gcongr
          rw [norm_pow, norm_inv, Complex.norm_two]
          exact pow_le_one₀ (by norm_num) (by norm_num)
      _ < s := by simpa using hv
  have hhalf : ∀ m : ℕ, k (((2 : ℂ)⁻¹ ^ m) • v) = ((2 : ℂ)⁻¹ ^ m) • k v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>

      set u : E := ((2 : ℂ)⁻¹ ^ (m + 1)) • v with hu
      have huu : u + u = ((2 : ℂ)⁻¹ ^ m) • v := by
        rw [hu, ← two_smul ℂ, smul_smul, pow_succ]
        congr 1
        field_simp
      have hus : u ∈ ball (0 : E) s := hhalf_mem (m + 1)
      have h2 : k (u + u) = k u + k u := hadd u u hus hus (by rw [huu]; exact hhalf_mem m)
      rw [huu, ih, ← two_smul ℂ] at h2

      have : k u = (2 : ℂ)⁻¹ • (((2 : ℂ)⁻¹ ^ m) • k v) := by
        rw [h2, smul_smul]; norm_num
      rw [this, smul_smul, pow_succ, mul_comm]

  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hA)
  simp only [zero_add, hk0, sub_zero] at hlo

  have key : ∀ ε : ℝ, 0 < ε → ‖k v - A v‖ ≤ ε * ‖v‖ := by
    intro ε hε
    have hev := hlo.def hε
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev

    obtain ⟨m, hm⟩ : ∃ m : ℕ, ((2 : ℝ)⁻¹) ^ m * ‖v‖ < η := by
      have ht : Tendsto (fun m : ℕ => ((2 : ℝ)⁻¹) ^ m * ‖v‖) atTop (𝓝 (0 * ‖v‖)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const _
      rw [zero_mul] at ht
      exact (ht.eventually (gt_mem_nhds hη)).exists
    have hmem : ((2 : ℂ)⁻¹ ^ m) • v ∈ ball (0 : E) η := by
      rw [mem_ball_zero_iff, norm_smul, norm_pow, norm_inv, Complex.norm_two]
      exact hm
    have h1 := hball _ hmem

    rw [hhalf m, map_smul, ← smul_sub, norm_smul, norm_smul, ← mul_assoc, mul_comm ε, mul_assoc] at h1
    have hpos : 0 < ‖(2 : ℂ)⁻¹ ^ m‖ := by
      rw [norm_pow, norm_inv, Complex.norm_two]; positivity
    exact le_of_mul_le_mul_left h1 hpos

  have : ‖k v - A v‖ ≤ 0 := by
    by_contra hcon
    push Not at hcon
    by_cases hv0 : ‖v‖ = 0
    · have := key 1 one_pos
      rw [hv0, mul_zero] at this
      exact absurd this (not_le.mpr hcon)
    · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
      have := key (‖k v - A v‖ / (2 * ‖v‖)) (by positivity)
      have : ‖k v - A v‖ ≤ ‖k v - A v‖ / 2 := by
        calc ‖k v - A v‖ ≤ ‖k v - A v‖ / (2 * ‖v‖) * ‖v‖ := this
          _ = ‖k v - A v‖ / 2 := by field_simp
      linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

theorem core {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (F : E → E → E)
    (e : E → E) (he0 : e 0 = 0) (heC : ContDiffAt ℂ 1 e 0)
    (hde : HasFDerivAt e (ContinuousLinearMap.id ℂ E) 0)
    (hinj : InjOn e (ball (0 : E) r))
    (hhom : ∀ v w : E, v ∈ ball (0 : E) r → w ∈ ball (0 : E) r → v + w ∈ ball (0 : E) r →
      e (v + w) = F (e v) (e w))
    {s : ℝ} (hs : 0 < s) (h : E → E) (hh0 : h 0 = 0)
    (hhhom : ∀ v w : E, v ∈ ball (0 : E) s → w ∈ ball (0 : E) s → v + w ∈ ball (0 : E) s →
      h (v + w) = F (h v) (h w))
    (A : E →L[ℂ] E) (hA : HasFDerivAt h A 0) :
    ∃ s' : ℝ, 0 < s' ∧ s' ≤ s ∧ ∀ v ∈ ball (0 : E) s', A v ∈ ball (0 : E) r ∧ h v = e (A v) := by

  have hde' : HasFDerivAt e ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) 0 := by
    simpa using hde
  set H := heC.toOpenPartialHomeomorph e hde' one_ne_zero with hHdef
  have hHcoe : (H : E → E) = e := rfl
  have h0s : (0 : E) ∈ H.source := heC.mem_toOpenPartialHomeomorph_source hde' one_ne_zero
  have h0t : (0 : E) ∈ H.target := by
    have := heC.image_mem_toOpenPartialHomeomorph_target hde' one_ne_zero
    rwa [he0] at this
  have hsymm0 : H.symm 0 = 0 := by
    have := H.left_inv h0s
    rwa [hHcoe, he0] at this
  have hsymmD : HasFDerivAt H.symm (ContinuousLinearMap.id ℂ E) 0 := by
    have := (heC.hasStrictFDerivAt' hde' one_ne_zero).to_localInverse.hasFDerivAt
    rw [he0] at this
    simp at this
    exact this

  set k : E → E := fun v => H.symm (h v) with hkdef
  have hk0 : k 0 = 0 := by simp [hkdef, hh0, hsymm0]
  have hkA : HasFDerivAt k A 0 := by
    have h1 : HasFDerivAt H.symm (ContinuousLinearMap.id ℂ E) (h 0) := by rw [hh0]; exact hsymmD
    have := h1.comp 0 hA
    simp at this
    exact this

  have hhc : ContinuousAt h 0 := hA.continuousAt
  have hkc : ContinuousAt k 0 := hkA.continuousAt
  have hN : h ⁻¹' H.target ∩ k ⁻¹' ball (0 : E) (r / 2) ∈ 𝓝 (0 : E) := by
    refine Filter.inter_mem (hhc.preimage_mem_nhds (by rw [hh0]; exact H.open_target.mem_nhds h0t)) ?_
    exact hkc.preimage_mem_nhds (by rw [hk0]; exact ball_mem_nhds _ (half_pos hr))
  obtain ⟨s₁, hs₁, hsub1⟩ := Metric.mem_nhds_iff.mp hN
  set s₂ : ℝ := min (s₁ / 2) s with hs₂def
  have hs₂p : 0 < s₂ := lt_min (half_pos hs₁) hs
  have hs₂s₁ : ∀ {v : E}, v ∈ ball (0 : E) s₂ → v ∈ ball (0 : E) s₁ := fun hv =>
    ball_subset_ball (le_trans (min_le_left _ _) (half_le_self (le_of_lt hs₁))) hv
  have hs₂s : ∀ {v : E}, v ∈ ball (0 : E) s₂ → v ∈ ball (0 : E) s := fun hv =>
    ball_subset_ball (min_le_right _ _) hv
  have hsum : ∀ {v w : E}, v ∈ ball (0 : E) s₂ → w ∈ ball (0 : E) s₂ → v + w ∈ ball (0 : E) s₁ := by
    intro v w hv hw
    rw [mem_ball_zero_iff] at hv hw ⊢
    have hv' : ‖v‖ < s₁ / 2 := lt_of_lt_of_le hv (min_le_left _ _)
    have hw' : ‖w‖ < s₁ / 2 := lt_of_lt_of_le hw (min_le_left _ _)
    calc ‖v + w‖ ≤ ‖v‖ + ‖w‖ := norm_add_le _ _
      _ < s₁ / 2 + s₁ / 2 := add_lt_add hv' hw'
      _ = s₁ := by ring
  have hek : ∀ {v : E}, v ∈ ball (0 : E) s₁ → e (k v) = h v := fun hv => by
    have := H.right_inv (hsub1 hv).1
    rwa [hHcoe] at this
  have hkr2 : ∀ {v : E}, v ∈ ball (0 : E) s₁ → k v ∈ ball (0 : E) (r / 2) := fun hv => (hsub1 hv).2
  have hr2r : ∀ {u : E}, u ∈ ball (0 : E) (r / 2) → u ∈ ball (0 : E) r := fun hu =>
    ball_subset_ball (half_le_self (le_of_lt hr)) hu
  have hsumr : ∀ {u u' : E}, u ∈ ball (0 : E) (r / 2) → u' ∈ ball (0 : E) (r / 2) → u + u' ∈ ball (0 : E) r := by
    intro u u' hu hu'
    rw [mem_ball_zero_iff] at hu hu' ⊢
    calc ‖u + u'‖ ≤ ‖u‖ + ‖u'‖ := norm_add_le _ _
      _ < r / 2 + r / 2 := add_lt_add hu hu'
      _ = r := by ring

  have hkadd : ∀ v w : E, v ∈ ball (0 : E) s₂ → w ∈ ball (0 : E) s₂ → v + w ∈ ball (0 : E) s₂ →
      k (v + w) = k v + k w := by
    intro v w hv hw hvw
    apply hinj (hr2r (hkr2 (hs₂s₁ hvw))) (hsumr (hkr2 (hs₂s₁ hv)) (hkr2 (hs₂s₁ hw)))
    rw [hek (hs₂s₁ hvw), hhhom v w (hs₂s hv) (hs₂s hw) (hs₂s hvw),
      hhom (k v) (k w) (hr2r (hkr2 (hs₂s₁ hv))) (hr2r (hkr2 (hs₂s₁ hw)))
        (hsumr (hkr2 (hs₂s₁ hv)) (hkr2 (hs₂s₁ hw))),
      hek (hs₂s₁ hv), hek (hs₂s₁ hw)]

  have hklin : ∀ v ∈ ball (0 : E) s₂, k v = A v := fun v hv =>
    eq_of_additive_of_hasFDerivAt hs₂p hk0 hkadd hkA hv
  refine ⟨s₂, hs₂p, min_le_right _ _, fun v hv => ⟨?_, ?_⟩⟩
  · rw [← hklin v hv]; exact hr2r (hkr2 (hs₂s₁ hv))
  · rw [← hklin v hv]; exact (hek (hs₂s₁ hv)).symm

end LocalGroupLawB2

end

open scoped ContDiff in
open LocalGroupLawB2 in
theorem solution
    {g : ℕ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (F : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ))

    (e : (Fin g → ℂ) → (Fin g → ℂ)) (he0 : e 0 = 0)
    (he : DifferentiableOn ℂ e (Metric.ball (0 : Fin g → ℂ) r))
    (hde : HasFDerivAt e (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0)
    (hinj : Set.InjOn e (Metric.ball (0 : Fin g → ℂ) r))
    (hmaps : Set.MapsTo e (Metric.ball (0 : Fin g → ℂ) r) (Metric.ball (0 : Fin g → ℂ) ρ))
    (hhom : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r → w ∈ Metric.ball (0 : Fin g → ℂ) r →
      v + w ∈ Metric.ball (0 : Fin g → ℂ) r → e (v + w) = F (e v) (e w))

    {s : ℝ} (hs : 0 < s) (h : (Fin g → ℂ) → (Fin g → ℂ)) (hh0 : h 0 = 0)
    (hh : DifferentiableOn ℂ h (Metric.ball (0 : Fin g → ℂ) s))
    (hhmaps : Set.MapsTo h (Metric.ball (0 : Fin g → ℂ) s) (Metric.ball (0 : Fin g → ℂ) ρ))
    (hhhom : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) s → w ∈ Metric.ball (0 : Fin g → ℂ) s →
      v + w ∈ Metric.ball (0 : Fin g → ℂ) s → h (v + w) = F (h v) (h w))
    (A : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (hA : HasFDerivAt h A 0) :
    ∃ s' : ℝ, 0 < s' ∧ s' ≤ s ∧
      ∀ v ∈ Metric.ball (0 : Fin g → ℂ) s', A v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ h v = e (A v) := by
  have heC : ContDiffAt ℂ 1 e 0 := by
    have hC : ContDiffOn ℂ ∞ e (Metric.ball (0 : Fin g → ℂ) r) :=
      Complex.contDiffOn_infty_of_differentiableOn_pi Metric.isOpen_ball he
    exact (hC.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (Metric.ball_mem_nhds _ hr)
  exact core hr hρ F e he0 heC hde hinj hhom hs h hh0 hhhom A hA

end S_LocalGroupLaw_exists_ball_eq_localExp_comp_fderiv_of_map_add
end P2MW
export P2MW.S_LocalGroupLaw_exists_ball_eq_localExp_comp_fderiv_of_map_add (solution)
