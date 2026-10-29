-- Prove2me | solution 1 for MIPStarRE.QPBT.pullingMeas_eval_consistencyDefect_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:22:39.530884+00:00
-- url     : https://prove2.me/submissions/4efb3917-3054-4aef-8586-4050ebf27ded

-- Generated proof for MIPStarRE.QPBT.pullingMeas_eval_consistencyDefect_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_BlockMeasurement
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_EncodingSupport
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_PullingMeasurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_kronecker
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_blockMeasurement_isProjective
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_consistencyDefect_placePlayers
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_le_opFamilyDistSq_of_projective
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_of_le_of_le
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_two_mul_consistencyDefect
import Theorems.Thm_MIPStarRE_QPBT_point_self_consistency_le
import Theorems.Thm_MIPStarRE_QPBT_pullingMeas_eval_point_consistent_alice
import Theorems.Thm_MIPStarRE_QPBT_pullingMeas_eval_point_consistent_bob

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.GlobalPairWitness
end MIPStarRE.QPBT.GlobalPairWitness
namespace MIPStarRE.QPBT.PauliKind
end MIPStarRE.QPBT.PauliKind
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Extraction/Observables.lean. -/
/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize blueprint
`lem:tildew-product-form`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize blueprint `lem:v-swap-conjugation`, from paper
lines 1687-1713.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Pulled-apart measurements and observables -/



namespace GlobalPairWitness



/-- The single-basis marginal remains a projective measurement. This is the
projectivity assertion implicit in blueprint
`def:s-w-marginals`, paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423`. Finite postprocessing
preserves projectivity, independently of the construction of the joint
measurement. -/
theorem marginalPoly_isProjective {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon delta : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S delta)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (w.marginalPoly side W) := by
  exact _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective
    (w.Smeas side) (w.projective side) W.selectPoly

end GlobalPairWitness





















/-! ## Swap conjugation -/























end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/PullingDefect.lean. -/
/-!
# Evaluated consistency of the difference-polynomial measurements

The exact overlap identities identify the consistency with the opposite
player's point measurement with the consistency supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the extraction obligations of this chapter; the
  global
  witness is supplied here, not constructed. This module was originally
  filed under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section





/-- Tensoring the strategy state with the two normalized EPR states preserves
the point-measurement consistency defect. This is the six-register form of
the point self-consistency used at `eq:qld-pulling-3`. -/
theorem point_consistencyDefect_psiHat {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
        (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeas .bob W u).effect a)) S.toStrategy.ψ := by
  exact S.consistencyDefect_placePlayers
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
    (fun u => S.pointMeas .alice W u) (fun u => S.pointMeas .bob W u)



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

























































































/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Extraction/PullingMeasurement.lean. -/
/-!
# Polynomial outcomes in the pulling argument

The joint measurement of a polynomial marginal and an ideal Pauli register
returns the difference between the polynomial and the encoding of the register.
Decoding this difference gives exactly the pulled-apart measurement. Polynomial
collision estimates apply to these representatives without an encoding-support
restriction on the original marginal.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1530-1605`,
  `eq:qld-pulling-11`, `eq:qld-pulling-12`, and the following symmetry argument.
- `docs/paper-gaps/qpbt_decoding-identity.tex`; only decoder linearity and its
  left-inverse identity are used here.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the `eq:qld-pulling-cons` extraction obligation;
  these
  auxiliary results do not assert it. This module was originally filed
  under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
- The collision estimate compares unequal difference polynomials under uniform
  evaluation.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus
open WinImplications

noncomputable section

open scoped Classical









/-- The joint effects are tensor products of orthogonal projections, and
postprocessing retains projectivity. -/
theorem pullingMeas_isProjective {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.pullingMeas w side W) := by
  apply _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective
  intro outcome
  exact _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
    (w.marginalPoly_isProjective side W outcome.1)
    ⟨by simp [IsIdempotentElem, _root_.MIPStarRE.QPBT.pauliRegisterMeas, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne,
        _root_.MIPStarRE.QPBT.pauliProj_mul_pauliProj],
      (_root_.MIPStarRE.QPBT.posSemidef_pauliProj W outcome.2).isHermitian⟩











end

end MIPStarRE.QPBT

/-!
# Evaluated consistency of the difference-polynomial measurements

The exact overlap identities identify the consistency with the opposite
player's point measurement with the consistency supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the extraction obligations of this chapter; the
  global
  witness is supplied here, not constructed. This module was originally
  filed under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {epsilon deltaG : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => S.placeSide .alice
          (((_root_.MIPStarRE.QPBT.pullingMeas w .alice W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a))
        (fun u a => S.placeSide .bob
          (((_root_.MIPStarRE.QPBT.pullingMeas w .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a))
        S.psiHat ≤ 12 * deltaG + 8 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * epsilon := by
  let mu := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
  let A := fun u => S.blockMeasurement .alice
    ((_root_.MIPStarRE.QPBT.pullingMeas w .alice W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u))
  let B := fun u => S.blockMeasurement .bob
    ((_root_.MIPStarRE.QPBT.pullingMeas w .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u))
  let PA := fun u => S.placedMeasurement .AA'
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (S.pointMeas .alice W u))
  let PB := fun u => S.placedMeasurement .BB'
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (S.pointMeas .bob W u))
  have hA := (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect mu A PB S.psiHat).trans
    (mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.pullingMeas_eval_point_consistent_alice w W)
      (by norm_num : (0 : ℝ) ≤ 2))
  have hB := (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect mu PA B S.psiHat).trans
    (mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.pullingMeas_eval_point_consistent_bob w W)
      (by norm_num : (0 : ℝ) ≤ 2))
  have hpoint : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (PA u).effect a)
      (fun u a => (PB u).effect a) S.psiHat ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * epsilon := by
    change _root_.MIPStarRE.QPBT.consistencyDefect mu
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤ _
    rw [_root_.MIPStarRE.QPBT.point_consistencyDefect_psiHat]
    exact _root_.MIPStarRE.QPBT.point_self_consistency_le S W
  have hP := (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect mu PA PB S.psiHat).trans
    (mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2))
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm] at hP
  have hAP := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le mu _ _ _ S.psiHat _ _ hA hP
  have hAB := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le mu _ _ _ S.psiHat _ _ hAP hB
  have hproj (side : _root_.MIPStarRE.QPBT.PlayerSide) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
      _root_.MIPStarRE.QPBT.Measurement.IsProjective (S.blockMeasurement side
        ((_root_.MIPStarRE.QPBT.pullingMeas w side W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u))) :=
    S.blockMeasurement_isProjective side _
      (_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (_root_.MIPStarRE.QPBT.pullingMeas_isProjective w side W) _)
  have hdef := _root_.MIPStarRE.QPBT.consistencyDefect_le_opFamilyDistSq_of_projective mu A B S.psiHat
    (hproj .alice) (hproj .bob)
  exact hdef.trans (hAB.trans (by ring_nf; rfl))
