-- Prove2me | solution 1 for NumberField.mixedEmbedding.contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3d0b45f0-0632-5db6-868d-3430c3a653b2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K] :
    (∀ (F : mixedSpace K → ℂ), ContDiff ℝ (⊤ : ℕ∞) F →
      ∀ (C₀ : Set (mixedSpace K)), IsCompact C₀ → (∀ y ∈ C₀, IsUnit y) → (∀ y, F y ≠ 0 → y ∈ C₀) →
        ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedSpace K => F (Ring.inverse y)) ∧
        IsCompact (Ring.inverse '' C₀) ∧ (∀ y ∈ Ring.inverse '' C₀, IsUnit y) ∧
        ∀ y : mixedSpace K, F (Ring.inverse y) ≠ 0 → y ∈ Ring.inverse '' C₀) ∧
    (∀ (g : mixedSpace K → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) g {y : mixedSpace K | IsUnit y} →
      ∀ (B : (Fin 2 → mixedSpace K) → ℂ), ContDiff ℝ (⊤ : ℕ∞) B → HasCompactSupport B →
      ∀ (Cp : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)), IsCompact Cp →
        (∀ p ∈ tsupport B, ∃ q ∈ Cp,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) →
        ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]) ∧
        HasCompactSupport (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]) ∧
        ∀ p ∈ tsupport (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]),
          ∃ q ∈ (fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (q.1, q.2 * q.1)) '' Cp,
            p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                  InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) := by
  have hUopen : IsOpen {y : mixedSpace K | IsUnit y} := Units.isOpen
  refine ⟨fun F hF C₀ hC₀ hC₀u hF0 => ?_, fun g hg B hB hBcs Cp hCp hBCp => ?_⟩
  ·
    have hcont : ContinuousOn (Ring.inverse : mixedSpace K → mixedSpace K) C₀ := by
      intro y hy
      obtain ⟨u, hu⟩ := hC₀u y hy
      rw [← hu]
      exact (NormedRing.inverse_continuousAt u).continuousWithinAt
    have hKc : IsCompact (Ring.inverse '' C₀) := hC₀.image_of_continuousOn hcont
    have hKu : ∀ y ∈ Ring.inverse '' C₀, IsUnit y := by
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨u, hu⟩ := hC₀u c hc
      rw [← hu, Ring.inverse_unit]
      exact Units.isUnit _
    have hvan : ∀ y : mixedSpace K, F (Ring.inverse y) ≠ 0 → y ∈ Ring.inverse '' C₀ := by
      intro y hy
      have hc := hF0 _ hy
      have hyu : IsUnit y := by
        by_contra h
        rw [Ring.inverse_non_unit _ h] at hc
        obtain ⟨u, hu⟩ := hC₀u _ hc
        exact not_isUnit_zero (hu ▸ Units.isUnit u)
      obtain ⟨w, rfl⟩ := hyu
      refine ⟨Ring.inverse (w : mixedSpace K), hc, ?_⟩
      rw [Ring.inverse_unit, Ring.inverse_unit, inv_inv]
    refine ⟨?_, hKc, hKu, hvan⟩
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : IsUnit y
    · obtain ⟨u, rfl⟩ := hy
      exact hF.contDiffAt.comp _ (contDiffAt_ringInverse ℝ u)
    · have hcl : IsClosed (Ring.inverse '' C₀) := hKc.isClosed
      have hy' : y ∉ Ring.inverse '' C₀ := fun h => hy (hKu y h)
      have hev : (fun y : mixedSpace K => F (Ring.inverse y)) =ᶠ[nhds y] fun _ => 0 := by
        filter_upwards [hcl.isOpen_compl.mem_nhds hy'] with y' hy'
        by_contra h
        exact hy' (hvan y' h)
      exact (contDiffAt_const.congr_of_eventuallyEq hev)
  ·
    let ι : (InfiniteAdeleRing K)ˣ → mixedSpace K := fun q =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K ((q : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
    have hιc : Continuous ι := by
      have h : (fun x : InfiniteAdeleRing K => InfiniteAdeleRing.ringEquiv_mixedSpace K x) =
          fun x => ((fun (v : {w : InfinitePlace K // IsReal w}) => Completion.extensionEmbeddingOfIsReal v.2 (x v)),
            (fun (v : {w : InfinitePlace K // IsComplex w}) => Completion.extensionEmbedding v.1 (x v))) := by
        funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
      have hc : Continuous fun x : InfiniteAdeleRing K => InfiniteAdeleRing.ringEquiv_mixedSpace K x := by
        rw [h]
        exact (continuous_pi fun v => (Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
            (continuous_apply v.1)).prodMk
          (continuous_pi fun v => (Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1))
      exact hc.comp Units.continuous_val
    have hιmul : ∀ a b : (InfiniteAdeleRing K)ˣ, ι (a * b) = ι a * ι b := fun a b => by
      simp only [ι, Units.val_mul, map_mul]
    have hιu : ∀ a : (InfiniteAdeleRing K)ˣ, IsUnit (ι a) := fun a => a.isUnit.map _
    let S : Set (Fin 2 → mixedSpace K) :=
      (fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => ![ι q.1, ι (q.2 * q.1)]) '' Cp
    have hS : IsCompact S := by
      refine hCp.image ?_
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact hιc.comp continuous_fst
      · exact hιc.comp (continuous_snd.mul continuous_fst)

    have hsupp : ∀ p : Fin 2 → mixedSpace K, g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)] ≠ 0 → p ∈ S := by
      intro p hp
      have hBne : B ![p 0, p 1 * Ring.inverse (p 0)] ≠ 0 := fun h => hp (by rw [h, mul_zero])
      obtain ⟨q, hq, hpq⟩ := hBCp _ (subset_tsupport _ (Function.mem_support.2 hBne))
      have h0 : p 0 = ι q.1 := by have := congr_fun hpq 0; (simp at this; exact this)
      have h1 : p 1 * Ring.inverse (p 0) = ι q.2 := by have := congr_fun hpq 1; (simp at this; exact this)
      refine ⟨q, hq, ?_⟩
      have hu0 : IsUnit (p 0) := by rw [h0]; exact hιu q.1
      have hp1 : p 1 = ι (q.2 * q.1) := by
        rw [hιmul, ← h1, ← h0, mul_assoc, Ring.inverse_mul_cancel _ hu0, mul_one]
      funext i
      fin_cases i
      · simpa using h0.symm
      · simpa using hp1.symm
    have hSu : ∀ p ∈ S, IsUnit (p 0) := by
      rintro _ ⟨q, -, rfl⟩
      simpa using hιu q.1
    refine ⟨?_, ?_, ?_⟩
    · rw [contDiff_iff_contDiffAt]
      intro p
      by_cases hp : IsUnit (p 0)
      · obtain ⟨u, hu⟩ := hp
        have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Fin 2 → mixedSpace K => Ring.inverse (p 0)) p := by
          have h := contDiffAt_ringInverse ℝ (n := (⊤ : ℕ∞)) u
          rw [hu] at h
          exact h.comp p (contDiffAt_apply (n := (⊤ : ℕ∞)) ℝ (mixedSpace K) (0 : Fin 2) p)
        have hg' : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Fin 2 → mixedSpace K => g (p 0)) p :=
          (hg.contDiffAt (hUopen.mem_nhds (hu ▸ u.isUnit))).comp p (contDiffAt_apply (n := (⊤ : ℕ∞)) ℝ (mixedSpace K) (0 : Fin 2) p)
        refine hg'.mul (hB.contDiffAt.comp p ?_)
        refine contDiffAt_pi' fun i => ?_
        fin_cases i
        · simpa using contDiffAt_apply (n := (⊤ : ℕ∞)) ℝ (mixedSpace K) (0 : Fin 2) p
        · simpa using (contDiffAt_apply (n := (⊤ : ℕ∞)) ℝ (mixedSpace K) (1 : Fin 2) p).mul hinv
      · have hcl : IsClosed S := hS.isClosed
        have hpS : p ∉ S := fun h => hp (hSu p h)
        have hev : (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]) =ᶠ[nhds p]
            fun _ => 0 := by
          filter_upwards [hcl.isOpen_compl.mem_nhds hpS] with p' hp'
          by_contra h
          exact hp' (hsupp p' h)
        exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact HasCompactSupport.intro hS fun p hp => by_contra fun h => hp (hsupp p h)
    · intro p hp
      have hsub : tsupport (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]) ⊆ S :=
        closure_minimal (fun p hp => hsupp p (Function.mem_support.1 hp)) hS.isClosed
      obtain ⟨q, hq, hpq⟩ := hsub hp
      refine ⟨(q.1, q.2 * q.1), ⟨q, hq, rfl⟩, ?_⟩
      rw [← hpq]

end S_NumberField_mixedEmbedding_contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units
end P2MW
export P2MW.S_NumberField_mixedEmbedding_contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units (solution)
