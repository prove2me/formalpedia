-- Prove2me | solution 1 for Kyprianou.Ch03.extendedStoppingDensityExhaustionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:31:05.129038+00:00
-- url     : https://prove2.me/submissions/8ae84b20-2639-4f05-bf8c-68d18498a01b

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_nonnegativeDensityExtendCutV1
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (tau : Omega → WithTop NNReal) (A : Set Omega) (g : Omega → Real)
    (hg : ∀ omega, 0 ≤ g omega)
    (hA : ∀ n : Nat, MeasurableSet
      (A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}))
    (hcut : ∀ n : Nat,
      let B := A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}
      AEMeasurable (Set.indicator B g) P ∧
        Q B = ∫⁻ omega, ENNReal.ofReal (Set.indicator B g omega) ∂P) :
    Q (A ∩ {omega : Omega | tau omega ≠ ⊤}) =
      ENNReal.ofReal (∫ omega,
        Set.indicator (A ∩ {eta : Omega | tau eta ≠ ⊤}) g omega ∂P) := by
  classical
  let B : ℕ → Set Omega := fun n => A ∩ {w | tau w ≤ ((n : NNReal) : WithTop NNReal)}
  have hm : Monotone B := by
    intro i j hij w hw
    have hc : (i : NNReal) ≤ (j : NNReal) := by exact_mod_cast hij
    exact ⟨hw.1, hw.2.trans (WithTop.coe_le_coe.mpr hc)⟩
  have hnon (n : ℕ) : ∀ w, 0 ≤ (B n).indicator g w :=
    Set.indicator_nonneg (fun w _ => hg w)
  have hi (n : ℕ) : Integrable ((B n).indicator g) P := by
    refine ⟨(hcut n).1.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (hnon n))).mpr ?_⟩
    rw [← (hcut n).2]
    exact measure_lt_top Q _
  have he (n : ℕ) : Q (B n) = ENNReal.ofReal (∫ w, (B n).indicator g w ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi n) (Filter.Eventually.of_forall (hnon n))]
    exact (hcut n).2
  have hu : (⋃ n, B n) = A ∩ {w | tau w ≠ ⊤} := by
    ext w
    simp only [Set.mem_iUnion, B, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, ha, hn⟩
      exact ⟨ha, ne_top_of_le_ne_top WithTop.coe_ne_top hn⟩
    · rintro ⟨ha, ht⟩
      obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp ht
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, ha, hx ▸ WithTop.coe_le_coe.mpr hn⟩
  rw [← hu]
  exact Kyprianou.Ch03.nonnegativeDensityExtendCutV1 P Q B g hA hm hg hi he
