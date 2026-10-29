-- Prove2me | solution 1 for MIPStarRE.QPBT.directCoordinate_failure_le_three_mul_rejection
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:44:57.286004+00:00
-- url     : https://prove2.me/submissions/51dd7a1b-41d4-4bbe-9b09-d51033623798

-- Generated proof for MIPStarRE.QPBT.directCoordinate_failure_le_three_mul_rejection.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_directCoordinate_failure_le_weightedFailure
import Theorems.Thm_MIPStarRE_QPBT_directLdBranchRejectionProbability_nonneg

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/GameValue.lean. -/
/-!
# Rejection probabilities for the directly indexed low-degree game

This module compares the rejection probability of the directly indexed game
with the branch weights used by the low individual degree test.
All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

The uniform distribution on the three ordered question types is specified in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`,
and its verifier is specified in the same file at lines 320-392.  The three
equal outer weights of the low individual degree test and its uniform role
choices are specified in `references/ldt-paper/test_definition.tex:10-67`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section









/-- Formalization-only expansion of a sum over the three low-degree question
types, in point, axis-line, and diagonal-line order.  This supports the uniform
branch calculation for the game in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`. -/
theorem sum_ldType (f : _root_.MIPStarRE.QPBT.LdType → ℝ) :
    ∑ t : _root_.MIPStarRE.QPBT.LdType, f t = f .point + f .aline + f .dline := by
  change (Finset.univ : Finset _root_.MIPStarRE.QPBT.LdType).sum f = _
  rw [show (Finset.univ : Finset _root_.MIPStarRE.QPBT.LdType) = {.point, .aline, .dline} by decide]
  simp [add_assoc]











end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Upstream.lean. -/
/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder



namespace LIDT
namespace MIPStarRE.LDT



/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, one_div, Finset.mul_sum]


end MIPStarRE.LDT
end LIDT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/PassConversion.lean. -/
/-!
# Pass conversion for the directly indexed low-degree game

This module converts a value bound for a projective strategy of the directly
indexed low-degree game into the hypothesis of the low individual degree
theorem for each coordinate strategy `directCoordinateProjStrat`.

The LDT failure probability gives weight `1/3` to point agreement and
`1/6` to each of the four oriented line-versus-point checks.  The branch
comparisons of `Transport.BranchComparison` and `Transport.DiagonalRecursion`
bound the point and axis-line branches by the corresponding direct branch
rejections and each diagonal branch by twice its direct branch rejection.  The
factor-three rejection calculus of `GameValue` gives the line branches half the
weight of the point branch, so the factor two is absorbed: a direct strategy of
value at least `1 - ε` has coordinate strategies of LDT failure at most
`3 * ε`, which is exactly `PassesLowIndividualDegreeTest (3 * ε)`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:300-311`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The failure comparison and the pass hypothesis -/

/-- The uniformly weighted rejection is one ninth of the sum over the nine
ordered type pairs. -/
private theorem directLdRejectionProbability_eq_sum (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) :
    _root_.MIPStarRE.QPBT.directLdRejectionProbability D S =
      (∑ types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType, _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types) / 9 := by
  unfold _root_.MIPStarRE.QPBT.directLdRejectionProbability
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_prod,
    show Fintype.card _root_.MIPStarRE.QPBT.LdType = 3 by decide, div_eq_inv_mul]
  norm_num













end

end MIPStarRE.QPBT

/-!
# Pass conversion for the directly indexed low-degree game

This module converts a value bound for a projective strategy of the directly
indexed low-degree game into the hypothesis of the low individual degree
theorem for each coordinate strategy `directCoordinateProjStrat`.

The LDT failure probability gives weight `1/3` to point agreement and
`1/6` to each of the four oriented line-versus-point checks.  The branch
comparisons of `Transport.BranchComparison` and `Transport.DiagonalRecursion`
bound the point and axis-line branches by the corresponding direct branch
rejections and each diagonal branch by twice its direct branch rejection.  The
factor-three rejection calculus of `GameValue` gives the line branches half the
weight of the point branch, so the factor two is absorbed: a direct strategy of
value at least `1 - ε` has coordinate strategies of LDT failure at most
`3 * ε`, which is exactly `PassesLowIndividualDegreeTest (3 * ε)`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:300-311`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## The failure comparison and the pass hypothesis -/

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).lowIndividualDegreeFailureProbability ≤
      3 * _root_.MIPStarRE.QPBT.directLdRejectionProbability D S := by
  letI := D.toLDTFieldModel
  have h := _root_.MIPStarRE.QPBT.directCoordinate_failure_le_weightedFailure D S hS r
  unfold _root_.MIPStarRE.QPBT.directLdLdtWeightedFailureProbability at h
  dsimp only at h
  rw [directLdRejectionProbability_eq_sum, Fintype.sum_prod_type]
  simp only [_root_.MIPStarRE.QPBT.sum_ldType]
  have hnonneg := _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg D S
  have hpp := hnonneg (.point, .point)
  have hpa := hnonneg (.point, .aline)
  have hpd := hnonneg (.point, .dline)
  have hap := hnonneg (.aline, .point)
  have haa := hnonneg (.aline, .aline)
  have had := hnonneg (.aline, .dline)
  have hdp := hnonneg (.dline, .point)
  have hda := hnonneg (.dline, .aline)
  have hdd := hnonneg (.dline, .dline)
  linarith
