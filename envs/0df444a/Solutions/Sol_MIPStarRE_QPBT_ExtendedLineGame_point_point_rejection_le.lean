-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.point_point_rejection_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:13:29.188723+00:00
-- url     : https://prove2.me/submissions/6c3bc9de-7696-490c-b52b-ee78a108c9ca

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.point_point_rejection_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PointPointRejection
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directPointExtendedQuestionEquiv_apply
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_point_branch_rejection_eq_consistencyDefect
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_stateQForm_pairState_eq_AA_prime_BA_prime_prime
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_le_opFamilyDistSq_of_projective
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_postprocess_le

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
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/ExtendedLineGame/PointPointRejection.lean. -/
/-!
# Point/point rejection for the extended direct game

This module bounds the point-agreement branch of the directly indexed
low-degree strategy by the self-consistency error of the supplied joint point
measurements.  The common extended point is transported by one coordinate
equivalence to the jointly uniform tuple `(x, z, alpha, beta)` before the
scalar coarse-graining is applied.

This is a formalization-only auxiliary for the supplied-witness route in the
proof of `lem:qld-4-7`; it does not construct the point witness or establish
the complete passing-value estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Issue Dengnifer/MIPStarRE-QPBT-bak#313.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}







/-- Question-dependent coarse-graining on opposite tensor factors cannot
increase their consistency defect. -/
private theorem consistencyDefect_dependent_postprocess_le
    {X Alpha Beta IA IB : Type*}
    [Fintype X] [DecidableEq X] [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype IA] [DecidableEq IA] [Fintype IB] [DecidableEq IB]
    (mu : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Alpha IA)
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Alpha IB) (psi : EuclideanSpace ℂ (IA × IB))
    (f : X → Alpha → Beta) :
    _root_.MIPStarRE.QPBT.consistencyDefect mu
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron (((A x).postprocess (f x)).effect b) 1)
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 (((B x).postprocess (f x)).effect b)) psi ≤
      _root_.MIPStarRE.QPBT.consistencyDefect mu
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) psi := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro x
  have h := _root_.MIPStarRE.QPBT.consistencyDefect_postprocess_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
    (fun _ => A x) (fun _ => B x) psi (f x)
  unfold _root_.MIPStarRE.QPBT.consistencyDefect at h
  simpa only [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const] using h

/-- A jointly uniform auxiliary coordinate can be discarded when both
operator families depend only on the first coordinate. -/
private theorem consistencyDefect_uniform_fst
    {X Y Alpha IA IB : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype IA] [DecidableEq IA] [Fintype IB] [DecidableEq IB]
    (A : X → Alpha → _root_.LIDT.MIPStarRE.Quantum.Op IA) (B : X → Alpha → _root_.LIDT.MIPStarRE.Quantum.Op IB)
    (psi : EuclideanSpace ℂ (IA × IB)) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (X × Y))
        (fun xy a => _root_.MIPStarRE.QPBT.heteroKron (A xy.1 a) 1)
        (fun xy a => _root_.MIPStarRE.QPBT.heteroKron 1 (B xy.1 a)) psi =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron (A x a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (B x a)) psi := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  let f : X → ℝ := fun x =>
    ∑ a : Alpha, ∑ b : Alpha,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv (IA × IB) ℂ).symm
          ((_root_.MIPStarRE.QPBT.heteroKron (A x a) 1 * _root_.MIPStarRE.QPBT.heteroKron 1 (B x b)).mulVec psi))).re
  change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (X × Y)) (fun xy => f xy.1) =
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) f
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_fst f













end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Points/PlacementSupport.lean. -/
/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
placement module proves EPR-exchange invariance for the involution
`(A' B'')(A'' B')`, which fixes `A` and `B`, in
`ProjectiveSetting.reindexState_eprCrossSwap_psiHat`; its use for
`lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Placements as reindexed tensor factors -/













/-! ## The placement is a unital `*`-homomorphism -/





















/-- A placed projective measurement is projective. -/
theorem placedMeasurement_isProjective (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p : _root_.MIPStarRE.QPBT.Placement) {α : Type*} [Fintype α]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p.side))
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (S.placedMeasurement p M) := by
  intro a
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · change S.place p (M.effect a) * S.place p (M.effect a) =
      S.place p (M.effect a)
    rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul, (hM a).isIdempotentElem.eq]
  · change star (S.place p (M.effect a)) = S.place p (M.effect a)
    rw [Matrix.star_eq_conjTranspose, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_conjTranspose,
      (hM a).isSelfAdjoint.isHermitian.eq]

end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Consistency.lean. -/
/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of blueprint
`def:consistency` and `def:strategy-distance`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-- A uniform consistency defect is invariant under a bijective relabeling of
its question type. -/
theorem consistencyDefect_uniform_question_equiv
    {X Y Outcome iota : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iota] [DecidableEq iota]
    (e : X ≃ Y) (A B : Y → Outcome → _root_.LIDT.MIPStarRE.Quantum.Op iota)
    (psi : EuclideanSpace ℂ iota) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x a => A (e x) a) (fun x a => B (e x) a) psi =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) A B psi := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  simpa using _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv e (fun x =>
    ∑ a : Outcome, ∑ b : Outcome,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv iota ℂ).symm
          (((A (e x) a) * (B (e x) b)).mulVec psi))).re)















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
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B























/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: pointwise equal operator families have equal state-dependent
distance. -/
theorem opFamilyDistSq_congr {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B A' B' : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ A' B' ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [hA x a, hB x a]







end MIPStarRE.QPBT.DistanceCalculus

/-!
# Point/point rejection for the extended direct game

This module bounds the point-agreement branch of the directly indexed
low-degree strategy by the self-consistency error of the supplied joint point
measurements.  The common extended point is transported by one coordinate
equivalence to the jointly uniform tuple `(x, z, alpha, beta)` before the
scalar coarse-graining is applied.

This is a formalization-only auxiliary for the supplied-witness route in the
proof of `lem:qld-4-7`; it does not construct the point witness or establish
the complete passing-value estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Issue Dengnifer/MIPStarRE-QPBT-bak#313.
-/



open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.ProjectiveSetting



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.point, .point) ≤ deltaQ := by
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.point_branch_rejection_eq_consistencyDefect lines]
  calc
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
        (fun q answer => _root_.MIPStarRE.QPBT.heteroKron
          (((points.Q .alice q.1.1 q.1.2).postprocess fun values =>
            some (q.2.1 * values.1 + q.2.2 * values.2)).effect answer) 1)
        (fun q answer => _root_.MIPStarRE.QPBT.heteroKron 1
          (((points.Q .bob q.1.1 q.1.2).postprocess fun values =>
            some (q.2.1 * values.1 + q.2.2 * values.2)).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
      rw [← _root_.MIPStarRE.QPBT.consistencyDefect_uniform_question_equiv
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P)]
      apply _root_.MIPStarRE.QPBT.consistencyDefect_congr <;> intro u answer
      · rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv_apply]
      · rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv_apply]
    _ ≤ _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
        (fun q values => _root_.MIPStarRE.QPBT.heteroKron
          ((points.Q .alice q.1.1 q.1.2).effect values) 1)
        (fun q values => _root_.MIPStarRE.QPBT.heteroKron 1
          ((points.Q .bob q.1.1 q.1.2).effect values))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
      exact consistencyDefect_dependent_postprocess_le
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
        (fun q => points.Q .alice q.1.1 q.1.2)
        (fun q => points.Q .bob q.1.1 q.1.2)
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting)
        (fun q values => some (q.2.1 * values.1 + q.2.2 * values.2))
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
        (fun xz values => _root_.MIPStarRE.QPBT.heteroKron
          ((points.Q .alice xz.1 xz.2).effect values) 1)
        (fun xz values => _root_.MIPStarRE.QPBT.heteroKron 1
          ((points.Q .bob xz.1 xz.2).effect values))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
      exact consistencyDefect_uniform_fst
        (X := (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (Y := _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P)
        (Alpha := _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P)
        (IA := setting.ExpandedLocalSpace .alice)
        (IB := setting.ExpandedLocalSpace .bob)
        (fun xz values => (points.Q .alice xz.1 xz.2).effect values)
        (fun xz values => (points.Q .bob xz.1 xz.2).effect values)
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting)
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
        (fun xz values =>
          (setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2)).effect values)
        (fun xz values =>
          (setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2)).effect values)
        setting.psiHat := by
      unfold _root_.MIPStarRE.QPBT.consistencyDefect
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro xz
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : a = b
      · simp [hab]
      · simp only [hab, if_false, _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
        rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect, _root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect,
          _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
        apply _root_.MIPStarRE.QPBT.ExtendedLineGame.stateQForm_pairState_eq_AA_prime_BA_prime_prime
        · exact (Matrix.nonneg_iff_posSemidef.mp
            ((points.Q .alice xz.1 xz.2).pos a)).isHermitian
        · exact (Matrix.nonneg_iff_posSemidef.mp
            ((points.Q .bob xz.1 xz.2).pos b)).isHermitian
    _ ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
        (fun xz values =>
          (setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2)).effect values)
        (fun xz values =>
          (setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2)).effect values)
        setting.psiHat := by
      apply _root_.MIPStarRE.QPBT.consistencyDefect_le_opFamilyDistSq_of_projective
      · intro xz
        exact setting.placedMeasurement_isProjective .AA'
          (points.Q .alice xz.1 xz.2) (points.projective .alice xz.1 xz.2)
      · intro xz
        exact setting.placedMeasurement_isProjective .BA''
          (points.Q .bob xz.1 xz.2) (points.projective .bob xz.1 xz.2)
    _ = _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
        (fun xz values =>
          setting.place .AA' ((points.Q .alice xz.1 xz.2).effect values))
        (fun xz values =>
          setting.place .BA'' ((points.Q .bob xz.1 xz.2).effect values))
        setting.psiHat := by
      apply _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_congr <;> intro xz values
      · exact setting.placedMeasurement_effect .AA'
          (points.Q .alice xz.1 xz.2) values
      · exact setting.placedMeasurement_effect .BA''
          (points.Q .bob xz.1 xz.2) values
    _ ≤ deltaQ := by
      simpa only [_root_.MIPStarRE.QPBT.Placement.side] using
        points.self_consistent .AA' .BA'' trivial
