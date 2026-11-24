-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:53:59.554943+00:00
-- url     : https://prove2.me/submissions/2389b78d-648a-462c-aeb1-863232dafd1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_integrableOn_wt
import Theorems.Thm_GlobalTheory_Hk_RealChar_min_le_sqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution {P Q : ℝ → ℝ} (hP : Measurable P) (hQ : Measurable Q) {ρ E : ℝ} (hE : 0 ≤ E)
    (h1 : ∀ t, 0 < t → |P t - ρ / t| ≤ E * min t (1 / t))
    (h2 : ∀ t, 0 < t → |Q t| ≤ E * min t (1 / t)) (hi : IntegrableOn Q (Set.Ioi 0))
    {v : ℝ} (hv : 0 < v) :
    ∫ w in Set.Ioi (0 : ℝ), P (v / w) * Q w / w ≤
      ρ / v * (∫ w in Set.Ioi (0 : ℝ), Q w) + E ^ 2 * Real.sqrt v * ∫ w in Set.Ioi (0 : ℝ), wt w := by
  set R : ℝ → ℝ := fun w => (P (v / w) - ρ / (v / w)) * Q w / w with hR
  have hRm : Measurable R := by simp only [hR]; fun_prop
  have hRb : ∀ w ∈ Set.Ioi (0 : ℝ), |R w| ≤ E ^ 2 * Real.sqrt v * wt w := by
    intro w hw
    have h0 : 0 < w := hw
    have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 h0
    simp only [hR]
    rw [abs_div, abs_mul, abs_of_pos h0]
    have e1 : |P (v / w) - ρ / (v / w)| ≤ E * (Real.sqrt v / Real.sqrt w) := by
      refine (h1 _ (by positivity)).trans ?_
      rw [← Real.sqrt_div hv.le]
      gcongr
      exact min_le_sqrt (by positivity)
    calc _ ≤ E * (Real.sqrt v / Real.sqrt w) * (E * min w (1 / w)) / w := by
          gcongr
          exact h2 w h0
      _ = _ := by unfold wt; field_simp
  have hw := integrableOn_wt.const_mul (E ^ 2 * Real.sqrt v)
  have hRi : IntegrableOn R (Set.Ioi 0) :=
    Integrable.mono' hw hRm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hRb))
  have e : ∫ w in Set.Ioi (0 : ℝ), P (v / w) * Q w / w
      = ∫ w in Set.Ioi (0 : ℝ), (ρ / v * Q w + R w) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    have h0 : 0 < w := hw
    simp only [hR]
    field_simp
    ring
  rw [e, integral_add (hi.const_mul _) hRi, integral_const_mul, ← integral_const_mul (E ^ 2 * Real.sqrt v)]
  gcongr ?_ + ?_
  · exact le_rfl
  · exact setIntegral_mono_on hRi hw measurableSet_Ioi fun w hw => (le_abs_self _).trans (hRb w hw)
end GlobalTheory.Hk.RealChar
