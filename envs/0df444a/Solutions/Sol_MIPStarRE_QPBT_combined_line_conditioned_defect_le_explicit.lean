-- Prove2me | solution 1 for MIPStarRE.QPBT.combined_line_conditioned_defect_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:32:41.078234+00:00
-- url     : https://prove2.me/submissions/260a057c-e187-426e-9ce7-9a41927aed32

-- Generated proof for MIPStarRE.QPBT.combined_line_conditioned_defect_le_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Lines_CombinedMeasurement
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingDistribution
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingMass
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_MIPStarRE_QPBT_Distribution_restrict_isProbability
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_consistencyDefect_bipartition
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_exists_opposite_bipartition
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_combined_points_conditioned_line_marginal_defect_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_nondegenerateLinePastingDist_collision_bound
import Theorems.Thm_MIPStarRE_QPBT_pasting_error_heterogeneous_explicit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Combining/Lines/CombinedMeasurement.lean. -/
/-!
# Combined X/Z line measurement

This module constructs the X-Z-X sandwich POVM used to combine one X-line
measurement with one Z-line measurement.  It also records the orientation of
the sandwich as a one-sided pasted measurement and the two axis-degree support
properties.

## References

The construction is the paired-line measurement in `lem:qld-xz-lines`, with
source `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:942-949`.
Its separate blueprint entries are `def:concrete-paired-line-measurement` and
`lem:concrete-paired-line-degree-support`; consistency remains the distinct
obligation `lem:combined-line-measurement-consistency`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section





/-- The constructed X-outer sandwich is the one-sided pasting output with
`G1 = Z`, `G2 = X`, and the polynomial answers exchanged. This identity fixes
the orientation in paper `14_analysis_of_the_pauli_basis_test.tex:943-961`;
it asserts no unproved consistency relation. -/
theorem ProjectiveSetting.combinedLineMeasurement_effect_eq_pastedMeasurement
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (lineX lineZ : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (fX fZ : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      _root_.MIPStarRE.QPBT.pastedMeasurement (S.lineMeasExp side .Z lineZ).effect
        (S.lineMeasExp side .X lineX).effect fZ fX := rfl





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/NondegeneratePastingDistribution.lean. -/
/-!
# Nondegenerate-line pasting distribution

This module constructs the proof-only normalized product line-point law whose
first sampled line has nonzero direction.

## References

The conditioning supports the pasting argument in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`, using
the normalized question laws from
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section





/-- The proof-only nondegenerate pasting question law is normalized. -/
theorem nondegenerateLinePastingDist_isProbability (L : _root_.MIPStarRE.QPBT.LdParams) :
    (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist L).IsProbability := by
  exact (_root_.MIPStarRE.QPBT.Distribution.restrict_isProbability _ _
    (_root_.MIPStarRE.QPBT.prod_linePointDist_nondegenerate_mass_pos L)).map _

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





























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: state-dependent squared distance between operator families is
nonnegative. -/
theorem opFamilyDistSq_nonneg {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    0 ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq μ M N ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x)
    (Finset.sum_nonneg fun a _ => sq_nonneg _)





























end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/Sandwich/Defs.lean. -/
/-! # Definitions for sandwiched measurements

This module defines the palindromic operator products and the conditional
collision predicate used by the sandwich and pasting lemmas.

## References

Blueprint `lem:ld-sandwich` and `lem:pasting`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus












/-! ### Tensor placements of measurements

The operator families compared in `lem:pasting` are placed on one factor of a
bipartite space. The two constructions below present such a placed family as a
measurement, so that the consistency calculus applies to it verbatim. -/









/-- The left placement of a projective measurement is projective.
Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.isProjective_leftPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ιB) M) := by
  intro a
  constructor
  · show _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1 =
      _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (_root_.MIPStarRE.QPBT.heteroKron (M.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ = _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1
    unfold _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M a,
      Matrix.conjTranspose_one]
















end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/ExpandedPlacement.lean. -/
/-!
# Placing operators on the expanded state

The four register placements of `def:symmetric-equivalents` put an operator of
one player's expanded local space on one of the register pairs `AA'`, `BA''`,
`BB'` and `AB''` of the expanded state `psiHat`.  This module records how such
a placement acts on `psiHat`: after the shuffle of `eq:def-psihat` the placed
operator is a threefold tensor product, so a factorized operator whose Pauli
factor is an isometry has the same state-dependent norm as its strategy factor
placed on the original state.  No symmetry between the two players is used;
each of the four placements is treated explicitly.

## References

The declarations support `def:symmetric-equivalents` and `lem:qld-comm-cons`
in `blueprint/src/chapter/ch14_qpbt_observables.tex:1002-1031` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-505`.
-/

@[expose] public section

-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Coordinate tensors -/











namespace ProjectiveSetting





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/





/-! ## The action of a placement on the expanded state -/

/-- The expanded state is the shuffle of the coordinate tensor of the strategy
state with the two EPR ancillas. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem psiHat_eq_reindexState (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    S.psiHat = _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.vecTensor S.toStrategy.ψ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))) := rfl

/-- The expanded strategy state is normalized. -/
theorem psiHat_norm (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : ‖S.psiHat‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_eq_reindexState, _root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq,
    _root_.MIPStarRE.QPBT.vecTensor_norm_eq, S.toStrategy.ψ_norm, _root_.MIPStarRE.QPBT.eprState_norm]
  norm_num

/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/



























end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/PointConsistency.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.pauliEdgeNonemptyPointConsistency
/-!
# Expanded point consistency and commutation

This module records the quantitative conclusions for the expanded point
measurements on each of the four register placements. No symmetry-transfer
principle is assumed: the four placements occur explicitly in the statements.

## References

The declarations formalize blueprint
`lem:qld-comm-cons`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:452-505`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section



/-! ## Consistency of the unexpanded point measurements -/





/-- Postprocessing a measurement after adjoining an identity register agrees
effectwise with adjoining that register after postprocessing. -/
theorem leftPlacedMeasurement_postprocess_effect
    {α β ι κ : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (f : α → β) (b : β) :
    ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := κ) M).postprocess f).effect b =
      _root_.MIPStarRE.QPBT.heteroKron ((M.postprocess f).effect b) (1 : _root_.LIDT.MIPStarRE.Quantum.Op κ) := by
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  change (∑ a ∈ Finset.univ.filter (fun a => f a = b),
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := κ) (M.effect a)) =
    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := κ)
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a)
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum _ _

-- The statements below are indexed by the fourfold iterated product of
-- `eq:def-psihat`; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default, which the
-- `synthInstance.maxSize` settings below supply declaration by declaration.


















end


end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/



/-- Every strategy value is at most one. This is an alias of the Games-layer
`MIPStarRE.QPBT.Strategy.value_le_one`, which carries the single proof; the name
is kept here so the existing callers of this layer resolve unchanged.
Formalization-only support for `def:tensor-product-value`, blueprint
`ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : S.value ≤ 1 :=
  _root_.MIPStarRE.QPBT.Strategy.value_le_one S

















end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/Construction.lean. -/
/-!
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section









/-- An unused tensor factor commutes with both the ordered sandwich and its
evaluation. This identity keeps the unused EPR pair when applying the
heterogeneous pasting theorem to the expanded state. -/
theorem evaluated_pastedMeasurement_heteroKron_one
    {firstAnswer secondAnswer result carrier unused : Type*}
    [Fintype firstAnswer] [Fintype secondAnswer] [DecidableEq result]
    [Fintype carrier] [DecidableEq carrier] [Fintype unused] [DecidableEq unused]
    (first : firstAnswer → _root_.LIDT.MIPStarRE.Quantum.Op carrier) (second : secondAnswer → _root_.LIDT.MIPStarRE.Quantum.Op carrier)
    (evaluate : firstAnswer → secondAnswer → result) (output : result) :
    (∑ firstAnswer, ∑ secondAnswer, if evaluate firstAnswer secondAnswer = output then
      _root_.MIPStarRE.QPBT.pastedMeasurement (fun answer => _root_.MIPStarRE.QPBT.heteroKron (first answer) (1 : _root_.LIDT.MIPStarRE.Quantum.Op unused))
        (fun answer => _root_.MIPStarRE.QPBT.heteroKron (second answer) (1 : _root_.LIDT.MIPStarRE.Quantum.Op unused)) firstAnswer secondAnswer
      else 0) =
    _root_.MIPStarRE.QPBT.heteroKron (∑ firstAnswer, ∑ secondAnswer,
      if evaluate firstAnswer secondAnswer = output then
        _root_.MIPStarRE.QPBT.pastedMeasurement first second firstAnswer secondAnswer else 0) (1 : _root_.LIDT.MIPStarRE.Quantum.Op unused) := by
  simp only [_root_.MIPStarRE.QPBT.pastedMeasurement, _root_.MIPStarRE.QPBT.heteroKron_mul, mul_one]
  ext row column
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.sum_apply, Matrix.ite_apply,
    Finset.sum_mul, ite_mul]



/-- Evaluating the actual X-outer paired-line POVM in Z-then-X answer order
gives precisely the evaluated sandwich in the one-sided pasting conclusion.
This is an identity for all descriptors and points, not only on the support
of the conditioned law. Source: `eq:qld-4-13-1`, paper
`14_analysis_of_the_pauli_basis_test.tex:950-963`. -/
theorem ProjectiveSetting.combinedLineMeasurement_evaluated_eq_pasted
    {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {error : ℝ} (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (lineX lineZ : _root_.MIPStarRE.QPBT.LineDesc params.toLdParams)
    (pointX pointZ : Fin params.m → _root_.MIPStarRE.QPBT.PauliScalar params)
    (output : Option (_root_.MIPStarRE.QPBT.PauliScalar params) × Option (_root_.MIPStarRE.QPBT.PauliScalar params)) :
    ((setting.combinedLineMeasurement side lineX lineZ).postprocess
      (fun polys => (_root_.MIPStarRE.QPBT.evalOpt lineZ pointZ polys.2, _root_.MIPStarRE.QPBT.evalOpt lineX pointX polys.1))).effect output =
    ∑ polyZ, ∑ polyX,
      if (_root_.MIPStarRE.QPBT.evalOpt lineZ pointZ polyZ, _root_.MIPStarRE.QPBT.evalOpt lineX pointX polyX) = output then
        _root_.MIPStarRE.QPBT.pastedMeasurement (setting.lineMeasExp side .Z lineZ).effect
          (setting.lineMeasExp side .X lineX).effect polyZ polyX else 0 := by
  classical
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [setting.combinedLineMeasurement_effect_eq_pastedMeasurement]
  exact Finset.sum_comm
















end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/SelfConsistency.lean. -/
/-!
# Self-consistency of the expanded line measurements

This module proves item 1 of the expanded-line consistency lemma on the two
opposite-placement bipartitions. The strategy line measurements are
self-consistent between the two players on average over the line-point
distribution, because a disagreement on a sampled line is rejected by the
corresponding self-loop of the Pauli basis test; the Pauli line projectors are
perfectly consistent on an EPR pair; and the data-processing inequality
transfers the product estimate to the addition postprocessing that defines the
expanded line measurement.

The module also records that the error parameter of a projective setting is
nonnegative, which is not assumed by the structure and is needed by the other
two items as well.

## References

The declarations formalize `enu:qld-comm-line-self-cons`, item 1 of
`lem:qld-comm-line-cons`, whose paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Self-consistency of the unexpanded line measurements -/











namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The error parameter -/

/-- The error parameter of a projective setting is nonnegative. Nothing in the
structure assumes this: it follows from the winning premise `1 - ε ≤ value`
together with the bound `value ≤ 1` satisfied by the value of every strategy.
Formalization-only auxiliary supplying the sign condition of the winning
implications used in items 2 and 3 of `lem:qld-comm-line-cons`. -/
theorem eps_nonneg (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : 0 ≤ ε := by
  have hv := _root_.MIPStarRE.QPBT.WinImplications.strategy_value_le_one S.toStrategy
  have hw := S.win
  linarith

/-! ## Placement of differences on the two bipartitions -/

-- The four-level product indices below exceed the default instance-search
-- size.







/-! ## Fine-product consistency on the two bipartitions -/





/-! ## Data processing and transport back to the six registers -/













end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400 in
set_option maxHeartbeats 800000 in
-- Heterogeneous pasting elaborates nested postprocesses with dependent measurement types.

theorem solution
    (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (error pointError : ℝ)
    (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error)
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting pointError)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
          _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist params.toLdParams)
            (fun query output => setting.place first
              (((points.Q first.side query.2.2 query.1.2.2).postprocess
                (fun pair => (some pair.2, some pair.1))).effect output))
            (fun query output => setting.place second
              (((setting.combinedLineMeasurement second.side query.1.1.1 query.1.1.2).postprocess
                (fun polys => (_root_.MIPStarRE.QPBT.evalOpt query.1.1.2 query.1.2.2 polys.2,
                  _root_.MIPStarRE.QPBT.evalOpt query.1.1.1 query.2.2 polys.1))).effect output)) setting.psiHat ≤
            _root_.MIPStarRE.QPBT.heterogeneousPastingError ((params.m * params.d : ℕ) /
              (Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ params.toLdParams) : ℝ))
              ((8 * pointError + 2080 * (error + _root_.MIPStarRE.QPBT.deltaLine error)) /
                _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass params.toLdParams) := by
  classical
  obtain ⟨equivalence, hfirst, hsecond⟩ :=
    setting.exists_opposite_bipartition first second hopposite
  have hpoint : 0 ≤ pointError :=
    (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _).trans
      (points.self_consistent first second hopposite)
  have hmass := (_root_.MIPStarRE.QPBT.prod_linePointDist_nondegenerate_mass_pos params.toLdParams).le
  have hextra : 0 ≤ 2080 * (error + _root_.MIPStarRE.QPBT.deltaLine error) :=
    mul_nonneg (by norm_num) (add_nonneg setting.eps_nonneg (Real.sqrt_nonneg _))
  have herror : 0 ≤ (8 * pointError + 2080 * (error + _root_.MIPStarRE.QPBT.deltaLine error)) /
      _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass params.toLdParams :=
    div_nonneg (by linarith) hmass
  have hbound := _root_.MIPStarRE.QPBT.pasting_error_heterogeneous_explicit
    (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist params.toLdParams)
    (fun (poly : _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d)) sample =>
      _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2 poly)
    (fun (poly : _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d)) sample =>
      _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2 poly)
    (fun pair => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
      (ιB := _root_.MIPStarRE.QPBT.PauliRegister params × _root_.MIPStarRE.QPBT.PauliRegister params)
      (setting.lineMeasExp second.side .Z pair.2))
    (fun pair => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
      (ιB := _root_.MIPStarRE.QPBT.PauliRegister params × _root_.MIPStarRE.QPBT.PauliRegister params)
      (setting.lineMeasExp second.side .X pair.1))
    (fun query => (points.Q first.side query.2.2 query.1.2.2).postprocess
      (fun pair => (some pair.2, some pair.1)))
    (_root_.MIPStarRE.QPBT.reindexState equivalence setting.psiHat)
    ((params.m * params.d : ℕ) / (Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ params.toLdParams) : ℝ))
    ((8 * pointError + 2080 * (error + _root_.MIPStarRE.QPBT.deltaLine error)) /
      _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass params.toLdParams)
    (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist_isProbability params.toLdParams)
    (by rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, setting.psiHat_norm]) (by positivity) herror
    (fun pair => _root_.MIPStarRE.QPBT.Measurement.isProjective_leftPlacement _
      (setting.lineMeasExp_isProjective second.side .X pair.1))
    (fun query => _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _)
    (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist_collision_bound params (params.m * params.d))
  simp_rw [_root_.MIPStarRE.QPBT.leftPlacedMeasurement_postprocess_effect] at hbound
  simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at hbound
  simp_rw [_root_.MIPStarRE.QPBT.evaluated_pastedMeasurement_heteroKron_one,
    setting.consistencyDefect_bipartition first second equivalence hfirst hsecond] at hbound
  have hmarginal := _root_.MIPStarRE.QPBT.combined_points_conditioned_line_marginal_defect_le_explicit
    params error pointError setting points first second hopposite
  unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.MIPStarRE.QPBT.nondegenerateLinePastingDist at hbound hmarginal ⊢
  simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.MIPStarRE.QPBT.ProjectiveSetting.lineEvalMeasExp]
    at hbound hmarginal ⊢
  have hresult := hbound hmarginal.1 hmarginal.2
  simp_rw [setting.combinedLineMeasurement_evaluated_eq_pasted]
  unfold _root_.MIPStarRE.QPBT.heterogeneousPastingError
  convert hresult using 1
