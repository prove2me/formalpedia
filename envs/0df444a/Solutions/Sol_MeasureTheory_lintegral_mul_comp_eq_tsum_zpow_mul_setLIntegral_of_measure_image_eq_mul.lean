-- Prove2me | solution 1 for MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b4cc0c79-36c3-5d40-9bf0-9d7714d3f62b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem solution
    {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) (T : Q ≃ᵐ Q)
    (κ : ℝ≥0∞) (hκ₀ : κ ≠ 0) (hκ : κ ≠ ∞)
    (hT : ∀ s : Set Q, MeasurableSet s → ν (T '' s) = κ * ν s)
    (m : Q → ℤ) (hm : Measurable m) (hmT : ∀ q, m (T q) = m q + 1)
    (h : Q → ℝ≥0∞) (hh : Measurable h) (hhT : ∀ q, h (T q) = h q)
    (Φ : ℤ → ℝ≥0∞) :
    ∫⁻ q, h q * Φ (m q) ∂ν = (∑' n : ℤ, κ ^ n * Φ n) * ∫⁻ q in {q | m q = 0}, h q ∂ν := by

  set A : ℤ → Set Q := fun n => {q | m q = n} with hA_def
  have hA : ∀ n, MeasurableSet (A n) := fun n => hm (measurableSet_singleton n)
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun q hqi hqj => hij ?_
    rw [hA_def] at hqi hqj
    exact hqi.symm.trans hqj
  have hunion : (⋃ n, A n) = Set.univ := by
    ext q; simp [hA_def]

  have hmap : ν.map T.symm = κ • ν := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply T.symm.measurable hs, Measure.smul_apply, smul_eq_mul, ← hT s hs,
      MeasurableEquiv.image_eq_preimage_symm]

  have hAsucc : ∀ n, A (n + 1) = T.symm ⁻¹' (A n) := by
    intro n; ext q
    simp only [hA_def, Set.mem_setOf_eq, Set.mem_preimage]
    have := hmT (T.symm q)
    rw [MeasurableEquiv.apply_symm_apply] at this
    rw [this]; exact add_left_inj 1

  have hhS : ∀ q, h (T.symm q) = h q := fun q => by
    conv_rhs => rw [← MeasurableEquiv.apply_symm_apply T q]
    exact (hhT _).symm

  set I : ℤ → ℝ≥0∞ := fun n => ∫⁻ q in A n, h q ∂ν with hI_def
  have hstep : ∀ n, I (n + 1) = κ * I n := by
    intro n
    simp only [hI_def]
    rw [hAsucc]
    calc ∫⁻ q in T.symm ⁻¹' A n, h q ∂ν
        = ∫⁻ q in T.symm ⁻¹' A n, h (T.symm q) ∂ν := by simp_rw [hhS]
      _ = ∫⁻ q in A n, h q ∂(ν.map T.symm) :=
          (setLIntegral_map (hA n) hh T.symm.measurable).symm
      _ = κ * ∫⁻ q in A n, h q ∂ν := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

  have hI : ∀ n : ℤ, I n = κ ^ n * I 0 := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
        rw [hstep, ih, ← mul_assoc, ENNReal.zpow_add hκ₀ hκ, zpow_one, mul_comm κ]
    | pred k ih =>
        have h1 : I (-(k : ℤ)) = κ * I (-(k : ℤ) - 1) := by
          rw [← hstep]; congr 1; ring
        have h2 : I (-(k : ℤ) - 1) = κ⁻¹ * I (-(k : ℤ)) := by
          rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hκ₀ hκ, one_mul]
        rw [h2, ih, ← mul_assoc, sub_eq_add_neg, ENNReal.zpow_add hκ₀ hκ, zpow_neg_one,
          mul_comm κ⁻¹]

  have hlevel : ∀ n, ∫⁻ q in A n, h q * Φ (m q) ∂ν = I n * Φ n := by
    intro n
    simp only [hI_def]
    rw [← lintegral_mul_const _ hh]
    refine setLIntegral_congr_fun (hA n) fun q hq => ?_
    rw [show m q = n from hq]
  have hsplit : ∫⁻ q, h q * Φ (m q) ∂ν = ∑' n, I n * Φ n := by
    rw [← setLIntegral_univ, ← hunion, lintegral_iUnion hA hdisj]
    exact tsum_congr hlevel
  rw [hsplit, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [hI n]
  simp only [hI_def, hA_def]
  ring

end S_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul
end P2MW
export P2MW.S_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul (solution)
