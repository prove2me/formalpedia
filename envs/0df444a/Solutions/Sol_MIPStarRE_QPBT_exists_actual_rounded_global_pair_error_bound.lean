-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_actual_rounded_global_pair_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:12:57.018416+00:00
-- url     : https://prove2.me/submissions/1a0e7e35-a2b7-4665-b59e-fc06c0ede91f

-- Generated proof for MIPStarRE.QPBT.exists_actual_rounded_global_pair_error_bound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Combining_PassingError
import Definitions.Def_QPBT_QPBT_Games_ErrorFunctions
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_actual_rounding_error_le_root
import Theorems.Thm_MIPStarRE_QPBT_exists_direct_global_pair_error_bound
import Theorems.Thm_MIPStarRE_QPBT_scale_deltaQld_le
import Theorems.Thm_MIPStarRE_QPBT_sqrt_deltaQld_le

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Absorption of the actual rounded polynomial-pair error

The point and line errors both enter low-degree soundness. The actual
projective rounding then incurs an eighth root. The unit cap is applied only
to the final consistency defect.

## References

Paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`.
This module composes the direct passing estimate with square-root closure for
the global error function.
-/



open MIPStarRE.QPBT

theorem solution (pointError : ℝ → ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : _root_.MIPStarRE.QPBT.IsPolyErr₂ lineError) (C a b : ℝ) (hC : 0 ≤ C)
    (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        let delta := _root_.MIPStarRE.QPBT.deltaLd a b
          (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope
            (pointError epsilon + C * (P.m : ℝ) *
              lineError epsilon ((P.m * P.d : ℕ) / (P.q : ℝ)))
            ((P.m * P.d : ℕ) / (P.q : ℝ))) P.q (2 * P.m + 2) P.d 1
        let eta := delta + Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) +
          2 * Real.sqrt (2 * delta)
        min 1 (8 * (4 * eta + 8 * pointError epsilon) +
          (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)) ≤
          _root_.MIPStarRE.QPBT.deltaQld A B epsilon P.m P.d P.q := by
  obtain ⟨A, B, hA, hB, hB1, hbound⟩ :=
    _root_.MIPStarRE.QPBT.exists_direct_global_pair_error_bound pointError hpoint lineError hline
      C a b 1 hC ha hb hb1 (by norm_num)
  refine ⟨1024 * A, B / 2 / 2 / 2, by linarith, by positivity, by linarith, ?_⟩
  intro P epsilon he delta eta
  let ratio : ℝ := ((P.m * P.d : ℕ) : ℝ) / P.q
  let passing := _root_.MIPStarRE.QPBT.directPassingErrorEnvelope
    (pointError epsilon + C * (P.m : ℝ) * lineError epsilon ratio) ratio
  let slack := _root_.MIPStarRE.QPBT.deltaLd a b (passing + epsilon) P.q (2 * P.m + 2) P.d 1
  let t := slack + Real.sqrt (pointError epsilon) + ratio
  have hr : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hpass : 0 ≤ passing := by dsimp [passing, _root_.MIPStarRE.QPBT.directPassingErrorEnvelope]; positivity
  have hp : 0 ≤ pointError epsilon := by
    obtain ⟨_, _, _, _, h⟩ := hpoint
    exact (h epsilon he).1
  have hs : 0 ≤ slack := by dsimp [slack, _root_.MIPStarRE.QPBT.deltaLd]; positivity
  have hd : 0 ≤ delta := by dsimp [delta, _root_.MIPStarRE.QPBT.deltaLd, _root_.MIPStarRE.QPBT.directPassingErrorEnvelope]; positivity
  have hds : delta ≤ slack := by
    change _root_.MIPStarRE.QPBT.deltaLd a b passing P.q (2 * P.m + 2) P.d 1 ≤ _
    dsimp [slack, _root_.MIPStarRE.QPBT.deltaLd]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (add_le_add
      (Real.rpow_le_rpow hpass (by linarith) hb.le) le_rfl) le_rfl
  have hdt : delta ≤ t := by dsimp [t]; linarith [Real.sqrt_nonneg (pointError epsilon)]
  have hpt : Real.sqrt (pointError epsilon) ≤ t := by dsimp [t]; linarith
  have hrt : ratio ≤ t := by dsimp [t]; linarith [Real.sqrt_nonneg (pointError epsilon)]
  have hratio : (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q) ≤ 30 * ratio := by
    have hm : (1 : ℝ) ≤ P.m := by exact_mod_cast P.one_le_m
    have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast P.hd
    dsimp [ratio]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    push_cast
    nlinarith
  have hcap : min 1 t ≤ _root_.MIPStarRE.QPBT.deltaQld A B epsilon P.m P.d P.q := by
    simpa only [one_mul] using hbound P epsilon he
  have hroot := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hcap))
  have hrootBound := (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt
    (_root_.MIPStarRE.QPBT.sqrt_deltaQld_le (P := P) hA.le he))).trans
      ((Real.sqrt_le_sqrt (_root_.MIPStarRE.QPBT.sqrt_deltaQld_le (P := P) (b := B / 2) hA.le he)).trans
        (_root_.MIPStarRE.QPBT.sqrt_deltaQld_le (P := P) (b := B / 2 / 2) hA.le he))
  refine (min_le_min_left 1 ?_).trans
    ((_root_.MIPStarRE.QPBT.actual_rounding_error_le_root hd hp hdt hpt hrt).trans
      ((mul_le_mul_of_nonneg_left (hroot.trans hrootBound) (by norm_num)).trans
        (_root_.MIPStarRE.QPBT.scale_deltaQld_le hA.le he (by norm_num : (1 : ℝ) ≤ 1024))))
  dsimp [eta]
  linarith
