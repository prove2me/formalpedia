-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_direct_global_pair_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:47:23.082717+00:00
-- url     : https://prove2.me/submissions/493db80f-4e15-4c2f-9e42-18fe2b0f76dc

-- Generated proof for MIPStarRE.QPBT.exists_direct_global_pair_error_bound.
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
import Theorems.Thm_MIPStarRE_QPBT_exists_direct_passing_polynomial_bound
import Theorems.Thm_MIPStarRE_QPBT_exists_global_pair_error_bound
import Theorems.Thm_MIPStarRE_QPBT_one_le_deltaLd_of_one_le_error

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectPassingErrorBounds.lean. -/
/-!
# Absorbing both errors of the directly indexed game

The conversion from combined measurements to a low-degree strategy has passing
error `3 * (sqrt (deltaQ + deltaL) + m * d / q)`. This module bounds its cap by
one while retaining the point error and the dimension factor in the line error.
It then absorbs low-degree soundness at that capped error into `deltaQld`.
These scalar estimates do not construct either measurement witness.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288,1402`
* Blueprint `lem:qld-4-7`
-/

@[expose] public section

namespace MIPStarRE.QPBT



/-- Low-degree soundness applied at the capped direct-game passing error has
the global polynomial-pair error form. The positive slack `error` permits a
soundness application even when the capped passing error is zero. The point
error occurs both in the passing error and in the subsequent square-root loss.

This auxiliary proves only the numerical substitution at paper `lem:qld-4-7`,
lines 1279--1288 and 1402. Constructing the strategy and the projective pair
measurement is handled separately by `exists_globalPairWitness`. -/
private theorem exists_capped_direct_global_pair_error_bound (pointError : ℝ → ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : _root_.MIPStarRE.QPBT.IsPolyErr₂ lineError)
    (C a b scale : ℝ) (hC : 0 ≤ C) (ha : 1 ≤ a)
    (hb : 0 < b) (hbOne : b ≤ 1) (hscale : 0 ≤ scale) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (error : ℝ), 0 ≤ error →
        min 1 (scale *
          (_root_.MIPStarRE.QPBT.deltaLd a b
            (min 1 (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope
              (pointError error + C * (P.m : ℝ) *
                lineError error ((P.m * P.d : ℕ) / (P.q : ℝ)))
              ((P.m * P.d : ℕ) / (P.q : ℝ))) + error)
            P.q (2 * P.m + 2) P.d 1 + Real.sqrt (pointError error) +
              ((P.m * P.d : ℕ) / (P.q : ℝ)))) ≤
          _root_.MIPStarRE.QPBT.deltaQld A B error P.m P.d P.q := by
  obtain ⟨passingError, hpassing, hbound⟩ :=
    _root_.MIPStarRE.QPBT.exists_direct_passing_polynomial_bound pointError hpoint lineError hline C hC
  obtain ⟨A, B, hA, hB, hBOne, habs⟩ :=
    _root_.MIPStarRE.QPBT.exists_global_pair_error_bound pointError hpoint passingError hpassing
      1 a b scale (by norm_num) ha hb hbOne hscale
  refine ⟨A, B, hA, hB, hBOne, ?_⟩
  intro P error herror
  have haNonneg : 0 ≤ a := by linarith
  have hratio : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by positivity
  have hpassNonneg : 0 ≤ min 1 (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope
      (pointError error + C * (P.m : ℝ) *
        lineError error ((P.m * P.d : ℕ) / (P.q : ℝ)))
      ((P.m * P.d : ℕ) / (P.q : ℝ))) := by
    unfold _root_.MIPStarRE.QPBT.directPassingErrorEnvelope
    positivity
  have hpass := hbound error _ (P.m : ℝ) herror hratio
    (by exact_mod_cast P.one_le_m)
  refine le_trans ?_ (habs P error herror)
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_left _ hscale
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  unfold _root_.MIPStarRE.QPBT.deltaLd
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg haNonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  apply Real.rpow_le_rpow (add_nonneg hpassNonneg herror) _ hb.le
  simpa only [one_mul] using add_le_add hpass (le_refl error)



end MIPStarRE.QPBT

/-!
# Absorbing both errors of the directly indexed game

The conversion from combined measurements to a low-degree strategy has passing
error `3 * (sqrt (deltaQ + deltaL) + m * d / q)`. This module bounds its cap by
one while retaining the point error and the dimension factor in the line error.
It then absorbs low-degree soundness at that capped error into `deltaQld`.
These scalar estimates do not construct either measurement witness.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288,1402`
* Blueprint `lem:qld-4-7`
-/



open MIPStarRE.QPBT

theorem solution (pointError : ℝ → ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : _root_.MIPStarRE.QPBT.IsPolyErr₂ lineError)
    (C a b scale : ℝ) (hC : 0 ≤ C) (ha : 1 ≤ a)
    (hb : 0 < b) (hbOne : b ≤ 1) (hscale : 0 ≤ scale) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (error : ℝ), 0 ≤ error →
        min 1 (scale *
          (_root_.MIPStarRE.QPBT.deltaLd a b
            (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope
              (pointError error + C * (P.m : ℝ) *
                lineError error ((P.m * P.d : ℕ) / (P.q : ℝ)))
              ((P.m * P.d : ℕ) / (P.q : ℝ)) + error)
            P.q (2 * P.m + 2) P.d 1 + Real.sqrt (pointError error) +
              ((P.m * P.d : ℕ) / (P.q : ℝ)))) ≤
          _root_.MIPStarRE.QPBT.deltaQld A B error P.m P.d P.q := by
  obtain ⟨A, B, hA, hB, hBOne, habs⟩ :=
    exists_capped_direct_global_pair_error_bound pointError hpoint lineError hline
      C a b (scale + 1) hC ha hb hbOne (by linarith)
  refine ⟨A, B, hA, hB, hBOne, ?_⟩
  intro P error herror
  have haNonneg : 0 ≤ a := by linarith
  let ratio : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  let passing := _root_.MIPStarRE.QPBT.directPassingErrorEnvelope
    (pointError error + C * (P.m : ℝ) * lineError error ratio) ratio
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hpassing : 0 ≤ passing := by dsimp [passing, _root_.MIPStarRE.QPBT.directPassingErrorEnvelope]; positivity
  have hbound := habs P error herror
  change min 1 ((scale + 1) *
    (_root_.MIPStarRE.QPBT.deltaLd a b (min 1 passing + error) P.q (2 * P.m + 2) P.d 1 +
      Real.sqrt (pointError error) + ratio)) ≤ _ at hbound
  change min 1 (scale *
    (_root_.MIPStarRE.QPBT.deltaLd a b (passing + error) P.q (2 * P.m + 2) P.d 1 +
      Real.sqrt (pointError error) + ratio)) ≤ _
  by_cases hsmall : passing ≤ 1
  · rw [min_eq_right hsmall] at hbound
    refine le_trans (min_le_min_left 1 ?_) hbound
    apply mul_le_mul_of_nonneg_right (by linarith)
    unfold _root_.MIPStarRE.QPBT.deltaLd
    exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg haNonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (add_nonneg (add_nonneg (Real.rpow_nonneg (add_nonneg hpassing herror) _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (by norm_num) _))) (Real.sqrt_nonneg _)) hratio
  · rw [min_eq_left (le_of_not_ge hsmall)] at hbound
    have hld : 1 ≤ _root_.MIPStarRE.QPBT.deltaLd a b (1 + error) P.q (2 * P.m + 2) P.d 1 :=
      _root_.MIPStarRE.QPBT.one_le_deltaLd_of_one_le_error ha hb.le (by linarith) (by omega) P.hd le_rfl
    have hsum : 1 ≤ _root_.MIPStarRE.QPBT.deltaLd a b (1 + error) P.q (2 * P.m + 2) P.d 1 +
        Real.sqrt (pointError error) + ratio := by
      linarith [Real.sqrt_nonneg (pointError error)]
    rw [min_eq_left (one_le_mul_of_one_le_of_one_le (by linarith) hsum)] at hbound
    exact (min_le_left _ _).trans hbound
