-- Prove2me | solution 1 for GlobalTheory.Hk.LogDeriv.absc_div_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:49.042404+00:00
-- url     : https://prove2.me/submissions/fdeb4bd4-ab8f-4adb-a78b-e2f689e86c10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
namespace GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation
private lemma norm_div_log_natCast_le_norm_div_log_two (x : ℂ) (n : ℕ) : ‖x / Complex.log n‖ ≤ ‖x‖ / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases lt_or_ge n 2 with hn | hn
  · have h0 : Complex.log (n : ℂ) = 0 := by
      interval_cases n <;> simp
    rw [h0, div_zero, norm_zero]
    exact div_nonneg (norm_nonneg _) hl2.le
  · have hge : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    rw [← Complex.natCast_log, norm_div, Complex.norm_of_nonneg (hl2.le.trans hge)]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hl2 hge
private lemma LSeriesSummable_div_log_of_LSeriesSummable {l : ℕ → ℂ} (hl : ∀ s : ℂ, 1 < s.re → LSeriesSummable l s)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => l n / Complex.log n) s := by
  refine Summable.of_norm_bounded (g := fun n => ‖LSeries.term l s n‖ / Real.log 2)
    ((summable_norm_iff.mpr (hl s hs)).div_const _) (fun n => ?_)
  simp only [LSeries.norm_term_eq]
  split_ifs
  · simp
  · rw [div_right_comm]
    gcongr
    exact norm_div_log_natCast_le_norm_div_log_two _ _
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
end GlobalTheory.Hk.LogDeriv
end

set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation
namespace GlobalTheory.Hk.LogDeriv
theorem _root_.solution {l : ℕ → ℂ} (h1 : l 1 = 0) (hl : ∀ s : ℂ, 1 < s.re → LSeriesSummable l s)
    {s : ℂ} (hs : 1 < s.re) : abscissaOfAbsConv (fun n => l n / Complex.log n) < s.re := by
  have h : abscissaOfAbsConv (fun n => l n / Complex.log n) ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      LSeriesSummable_div_log_of_LSeriesSummable hl (by simpa using hy)
  exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr hs)
end GlobalTheory.Hk.LogDeriv
