-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_ordered_estimates_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:32:41.48797+00:00
-- url     : https://prove2.me/submissions/af21e062-bc46-4839-9823-280d6cf50c56

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_ordered_estimates_explicit.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_AnyStrategySoundness
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PointPointRejection
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RoundedPolynomialEstimates
import Definitions.Def_QPBT_QPBT_Combining_PassingError
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_MeasurementCompression
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Upstream
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_CombinedPointsWitness_ordered_dist_le
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directPointExtendedQuestionEquiv_apply
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_stateQForm_pairState_eq_AA_prime_BA_prime_prime
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_stateQForm_pairState_eq_AB_prime_prime_BB_prime
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_strategy_value_ge_directPassingErrorEnvelope
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_padState_compressAt
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_postprocess_le
import Theorems.Thm_MIPStarRE_QPBT_direct_ld_soundness_of_k_eq_one_explicit
import Theorems.Thm_MIPStarRE_QPBT_projective_rounding_preserves_postprocessed_consistency_left
import Theorems.Thm_MIPStarRE_QPBT_projective_rounding_preserves_postprocessed_consistency_right

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
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
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.Measurement
end MIPStarRE.QPBT.Measurement

/- Source helpers from QPBT/Combining/PassingError.lean. -/
/-! # Capped scalar envelope for direct-game error bounds

This module gives a concrete polynomial envelope for a scalar expression assembled from
seven prospective rejection bounds in the directly indexed extended-line game. It is a
formalization-only arithmetic auxiliary: it does not prove that any game branch satisfies
one of these bounds, nor does it prove a passing-value theorem.

The cap by one records the independent fact that a rejection probability is at most one.
It is essential for the polynomial-error contract: the uncapped function
`2 * x + Real.sqrt x + y` cannot be bounded by one positive power of `x` both near zero
and at infinity.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 and arithmetic issue
  Dengnifer/MIPStarRE-QPBT-bak#326
-/

@[expose] public section

namespace MIPStarRE.QPBT





/-- A positive second input makes the direct passing-error envelope positive. -/
theorem directPassingErrorEnvelope_pos (x y : ℝ) (hy : 0 < y) :
    0 < _root_.MIPStarRE.QPBT.directPassingErrorEnvelope x y := by
  dsimp [_root_.MIPStarRE.QPBT.directPassingErrorEnvelope]
  nlinarith [Real.sqrt_nonneg x]







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

/- Source helpers from QPBT/Games/DistanceTheorems/RoundingTransport.lean. -/
/-!
# Projective rounding through outcome postprocessing

Consistent complete POVMs on two possibly different local spaces have projective
roundings on those same spaces. Their consistency with an opposite-player POVM
survives every question-dependent outcome map, with error
`δ + sqrt (220 * δ^(1/4)) + 2 * sqrt (δ + η)` when the original consistency errors
are at most `δ` and `η`. The estimate is independent of both local dimensions and
the number of outcomes.

These are formalization-only auxiliary results for the compression and rounding
argument preceding the polynomial-support argument in `lem:qld-4-7`. They do not
construct the global polynomial-pair measurement.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:135-145`, `lem:ortho`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`,
  in the proof of `lem:qld-4-7`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`,
  `fact:triangle-for-simeq` and `fact:data-processing`
- Issue Dengnifer/MIPStarRE-QPBT-bak#278
- `audits/2026-09-06_rounding_transport.md`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Formalization-only question-dependent form of `fact:data-processing`.
Applying the same outcome map to both players at each question cannot increase
their consistency defect. No normalization of the distribution or state is needed. -/
theorem consistencyDefect_postprocess_question_le {X α β ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA)
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (f : X → α → β) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron (((A x).postprocess (f x)).effect b) 1)
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 (((B x).postprocess (f x)).effect b)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro x
  simpa only [_root_.MIPStarRE.QPBT.consistencyDefect,
    _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability Unit)] using
    _root_.MIPStarRE.QPBT.consistencyDefect_postprocess_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ => A x) (fun _ => B x) ψ (f x)



















/-- Formalization-only simultaneous rounding and transport for the compression
step of `lem:qld-4-7`. A single pair of complete projective measurements on the
original heterogeneous spaces satisfies the distance bounds and both consistency
estimates for every finite question type, probability distribution, and
question-dependent outcome map. Each comparison family requires only its own
consistency bound against the corresponding unrounded POVM. The hypotheses are
`‖ψ‖ = 1`, `δ ≥ 0`, and the original cross-player consistency bound; no range
restriction on the comparison error or outcome-cardinality factor is imposed. -/
theorem projective_rounding_preserves_postprocessed_consistency
    {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcons : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (A.effect a) 1)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (B.effect a)) ψ ≤ δ) :
    ∃ PA : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA, ∃ PB : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB,
      _root_.MIPStarRE.QPBT.Measurement.IsProjective PA ∧ _root_.MIPStarRE.QPBT.Measurement.IsProjective PB ∧
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (PA.effect a) 1)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (A.effect a) 1) ψ ≤
          220 * Real.rpow δ (1 / 4 : ℝ) ∧
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (PB.effect a))
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (B.effect a)) ψ ≤
          220 * Real.rpow δ (1 / 4 : ℝ) ∧
      ∀ {X β : Type*} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]
        (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X), μ.IsProbability → ∀ (f : X → α → β),
        (∀ (N : X → _root_.LIDT.MIPStarRE.Quantum.Measurement β ιB) (η : ℝ),
          _root_.MIPStarRE.QPBT.consistencyDefect μ
            (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((A.postprocess (f x)).effect b) 1)
            (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((N x).effect b)) ψ ≤ η →
          _root_.MIPStarRE.QPBT.consistencyDefect μ
            (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((PA.postprocess (f x)).effect b) 1)
            (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((N x).effect b)) ψ ≤
              δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
                2 * Real.sqrt (δ + η)) ∧
        (∀ (N : X → _root_.LIDT.MIPStarRE.Quantum.Measurement β ιA) (η : ℝ),
          _root_.MIPStarRE.QPBT.consistencyDefect μ
            (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((N x).effect b) 1)
            (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤ η →
          _root_.MIPStarRE.QPBT.consistencyDefect μ
            (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((N x).effect b) 1)
            (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((PB.postprocess (f x)).effect b)) ψ ≤
              δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
                2 * Real.sqrt (δ + η)) := by
  obtain ⟨PA, hPA, hAdist, hAtransport⟩ :=
    _root_.MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_left ψ hψ A B δ hδ hcons
  obtain ⟨PB, hPB, hBdist, hBtransport⟩ :=
    _root_.MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_right ψ hψ A B δ hδ hcons
  refine ⟨PA, PB, hPA, hPB, hAdist, hBdist, ?_⟩
  intro X β _ _ _ _ μ hμ f
  exact ⟨hAtransport μ hμ f, hBtransport μ hμ f⟩

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































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/MeasurementCompression.lean. -/
/-!
# Ground-slice compression of measurements

This module restricts a POVM on a product space to one distinguished ancillary
coordinate. It also records that this restriction commutes with deterministic
outcome postprocessing, recovers a POVM from its one-measurement Naimark
dilation, and preserves consistency defects evaluated on the correspondingly
padded bipartite state.

The construction supports the pullback after the first paragraph of the proof
of paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1289`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace LIDT
namespace MIPStarRE.Quantum.Measurement





/-- Restricting a POVM to a fixed ancillary coordinate commutes with
deterministic relabeling of its outcomes. -/
theorem compressAt_postprocess
    {A B I κ : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] [Fintype κ] [DecidableEq κ]
    (k₀ : κ) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement A (I × κ)) (f : A → B) :
    (M.postprocess f).compressAt k₀ = (M.compressAt k₀).postprocess f := by
  classical
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro b
  ext i j
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.compressAt_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    Matrix.submatrix_apply, Matrix.sum_apply]

end MIPStarRE.Quantum.Measurement
end LIDT

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

namespace Measurement

/-- Compressing the completed one-measurement Naimark dilation at its
distinguished `none` coordinate recovers the original POVM. -/
theorem compressAt_dilatedMeasurement
    {A I : Type} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I]
    (a₀ : A) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement A I) :
    (_root_.MIPStarRE.QPBT.dilatedMeasurement a₀ M).compressAt none = M := by
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro a
  ext i j
  exact _root_.MIPStarRE.QPBT.dilatedMeasurement_compression a₀ a M i j

end Measurement



end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean. -/
/-!
# Direct low-degree soundness for arbitrary strategies

This module transports directly indexed low-degree soundness at simultaneity
parameter `1` from projective strategies to arbitrary strategies. Both local
measurement families are dilated by the existing one-measurement Naimark
construction. The polynomial-tuple POVMs returned by projective soundness are
then compressed to the original player carriers at the distinguished ancillary
coordinate.

Ground-slice compression preserves all three consistency defects exactly, so
the error function and its universal constants are unchanged. The compressed
polynomial POVMs are not asserted to be projective.

## Main result

* `exists_direct_ld_soundness_of_k_eq_one_any_strategy` removes the projectivity
  premise from the formalization-only direct `k = 1` soundness route.

## References

The projective soundness input formalizes the shape of paper
`lem:ld-soundness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`.
The Naimark transport supports the first paragraph of the proof of paper
`lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`.
This module is formalization-only support and does not claim completion of that lemma.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section



/-- Every local measurement of the dilated direct-game strategy is projective. -/
private theorem directLdNaimarkStrategy_isProjective (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) : (directLdNaimarkStrategy D S).IsProjective :=
  _root_.MIPStarRE.QPBT.paddedStrategy_isProjective S none none _ _
    (fun question => _root_.MIPStarRE.QPBT.dilatedMeasurement_isProjective
      (default : _root_.MIPStarRE.QPBT.DirectLdAnswer D) (S.A question))
    (fun question => _root_.MIPStarRE.QPBT.dilatedMeasurement_isProjective
      (default : _root_.MIPStarRE.QPBT.DirectLdAnswer D) (S.B question))

/-- The direct-game value is unchanged by the two local Naimark dilations. -/
private theorem directLdNaimarkStrategy_value (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) : (directLdNaimarkStrategy D S).value = S.value :=
  _root_.MIPStarRE.QPBT.paddedStrategy_value S none none _ _
    (fun question answer => _root_.MIPStarRE.QPBT.dilatedMeasurement_compression
      (default : _root_.MIPStarRE.QPBT.DirectLdAnswer D) answer (S.A question))
    (fun question answer => _root_.MIPStarRE.QPBT.dilatedMeasurement_compression
      (default : _root_.MIPStarRE.QPBT.DirectLdAnswer D) answer (S.B question))

/-- Compressing Alice's dilated point measurement after point-answer
postprocessing recovers the original postprocessed point measurement. -/
private theorem directLdNaimarkStrategy_pointA_compress (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (question : _root_.MIPStarRE.QPBT.DirectLdQuestion D) :
    (((directLdNaimarkStrategy D S).A question).postprocess
        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).compressAt none =
      (S.A question).postprocess (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D) := by
  change ((_root_.MIPStarRE.QPBT.dilatedMeasurement (default : _root_.MIPStarRE.QPBT.DirectLdAnswer D) (S.A question)).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).compressAt none = _
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.compressAt_postprocess,
    _root_.MIPStarRE.QPBT.Measurement.compressAt_dilatedMeasurement]

/-- Compressing Bob's dilated point measurement after point-answer
postprocessing recovers the original postprocessed point measurement. -/
private theorem directLdNaimarkStrategy_pointB_compress (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (question : _root_.MIPStarRE.QPBT.DirectLdQuestion D) :
    (((directLdNaimarkStrategy D S).B question).postprocess
        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).compressAt none =
      (S.B question).postprocess (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D) := by
  change ((_root_.MIPStarRE.QPBT.dilatedMeasurement (default : _root_.MIPStarRE.QPBT.DirectLdAnswer D) (S.B question)).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).compressAt none = _
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.compressAt_postprocess,
    _root_.MIPStarRE.QPBT.Measurement.compressAt_dilatedMeasurement]

/-- Compress concrete polynomial measurements for the dilated strategy back to
the original player spaces while preserving all three consistency bounds. -/
private theorem directLdNaimarkStrategy_compress_soundness
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (bound : ℝ)
    (GA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D (directLdNaimarkStrategy D S).ιA)
    (GB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D (directLdNaimarkStrategy D S).ιB)
    (h1 : _root_.MIPStarRE.QPBT.consistencyDefect
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
        ((((directLdNaimarkStrategy D S).A
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
            (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
        ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
      (directLdNaimarkStrategy D S).ψ ≤ bound)
    (h2 : _root_.MIPStarRE.QPBT.consistencyDefect
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
        ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
        ((((directLdNaimarkStrategy D S).B
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
            (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
      (directLdNaimarkStrategy D S).ψ ≤ bound)
    (h3 : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
      (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
      (directLdNaimarkStrategy D S).ψ ≤ bound) :
    ∃ GA0 : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιA,
      ∃ GB0 : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιB,
        _root_.MIPStarRE.QPBT.consistencyDefect
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
              (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
              ((GB0.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
            S.ψ ≤ bound ∧
        _root_.MIPStarRE.QPBT.consistencyDefect
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
              ((GA0.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
              (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
            S.ψ ≤ bound ∧
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA0.effect g) 1)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB0.effect g)) S.ψ ≤ bound := by
  let GA0 : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιA :=
    GA.compressAt (none : Option (_root_.MIPStarRE.QPBT.directLdGame D).AnswerA)
  let GB0 : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιB :=
    GB.compressAt (none : Option (_root_.MIPStarRE.QPBT.directLdGame D).AnswerB)
  refine ⟨GA0, GB0, ?_, ?_, ?_⟩
  · have htransport :
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
              ((((directLdNaimarkStrategy D S).A
                (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                  (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
              ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
            (directLdNaimarkStrategy D S).ψ =
          _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
              (((((directLdNaimarkStrategy D S).A
                (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                  (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).compressAt none).effect outcome) 1)
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
              (((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).compressAt none).effect outcome))
            S.ψ := by
      change _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
            ((((directLdNaimarkStrategy D S).A
              (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
            ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
          (_root_.MIPStarRE.QPBT.padState none none S.ψ) = _
      exact _root_.MIPStarRE.QPBT.consistencyDefect_padState_compressAt _ _ _ none none S.ψ
    calc
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
            (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
              (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
            ((GB0.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome)) S.ψ =
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
            (((((directLdNaimarkStrategy D S).A
              (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).compressAt none).effect outcome) 1)
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
            (((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).compressAt none).effect outcome))
          S.ψ := by
            apply _root_.MIPStarRE.QPBT.consistencyDefect_congr
            · intro u outcome
              rw [directLdNaimarkStrategy_pointA_compress]
            · intro u outcome
              dsimp only [GB0]
              rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.compressAt_postprocess]
      _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
            ((((directLdNaimarkStrategy D S).A
              (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
            ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
          (directLdNaimarkStrategy D S).ψ := htransport.symm
      _ ≤ bound := h1
  · have htransport :
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
              ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
              ((((directLdNaimarkStrategy D S).B
                (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                  (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
            (directLdNaimarkStrategy D S).ψ =
          _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
              (((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).compressAt none).effect outcome) 1)
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
              (((((directLdNaimarkStrategy D S).B
                (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                  (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).compressAt none).effect outcome))
            S.ψ := by
      change _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
            ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
            ((((directLdNaimarkStrategy D S).B
              (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
          (_root_.MIPStarRE.QPBT.padState none none S.ψ) = _
      exact _root_.MIPStarRE.QPBT.consistencyDefect_padState_compressAt _ _ _ none none S.ψ
    calc
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
            ((GA0.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
            (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
              (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome)) S.ψ =
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
            (((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).compressAt none).effect outcome) 1)
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
            (((((directLdNaimarkStrategy D S).B
              (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).compressAt none).effect outcome))
          S.ψ := by
            apply _root_.MIPStarRE.QPBT.consistencyDefect_congr
            · intro u outcome
              dsimp only [GA0]
              rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.compressAt_postprocess]
            · intro u outcome
              rw [directLdNaimarkStrategy_pointB_compress]
      _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
            ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
          (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
            ((((directLdNaimarkStrategy D S).B
              (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
          (directLdNaimarkStrategy D S).ψ := htransport.symm
      _ ≤ bound := h2
  · have htransport :
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
            (directLdNaimarkStrategy D S).ψ =
          _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron ((GA.compressAt none).effect g) 1)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 ((GB.compressAt none).effect g)) S.ψ := by
      change _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g)) (_root_.MIPStarRE.QPBT.padState none none S.ψ) = _
      exact _root_.MIPStarRE.QPBT.consistencyDefect_padState_compressAt
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) (fun _ => GA) (fun _ => GB) none none S.ψ
    calc
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA0.effect g) 1)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB0.effect g)) S.ψ =
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron ((GA.compressAt none).effect g) 1)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 ((GB.compressAt none).effect g)) S.ψ := by
            rfl
      _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
          (directLdNaimarkStrategy D S).ψ := htransport.symm
      _ ≤ bound := h3

/-- Formalization-only soundness transport for the directly indexed low-degree
game at simultaneity parameter `1`, with no projectivity premise on the input
strategy.

Apply Naimark dilation to both question-indexed POVM families, use
`exists_direct_ld_soundness_of_k_eq_one` on the resulting projective strategy,
and compress its two polynomial-tuple POVMs at the distinguished ancillary
coordinates. The padded-state defect identity preserves the two point versus
polynomial bounds and the polynomial self-consistency bound exactly, with the
same witnesses `a`, `b`, and `deltaLd` as the projective theorem.

This theorem is formalization-only support for the Naimark step in the proof of paper
`lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`.
Its separate blueprint entry is `thm:qld-direct-soundness-any-strategy`.
It does not assert projectivity of the compressed POVMs and does not add a
hypothesis to any paper-labelled theorem. -/
theorem direct_ld_soundness_of_k_eq_one_any_strategy_explicit :
    ∀ (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ε : ℝ), D.k = 1 → 0 < ε →
        ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D), 1 - ε ≤ S.value →
          ∃ GA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιA,
            ∃ GB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιB,
              _root_.MIPStarRE.QPBT.consistencyDefect
                  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron
                      (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron 1
                      ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
                  S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
                    _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              _root_.MIPStarRE.QPBT.consistencyDefect
                  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron
                      ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron 1
                      (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
                  S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
                    _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
                  (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
                  (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
                  S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
                    _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower ε D.q D.m D.d D.k := by
  intro D ε hk hε S hwin
  have hwin' : 1 - ε ≤ (directLdNaimarkStrategy D S).value := by
    rw [directLdNaimarkStrategy_value]
    exact hwin
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    _root_.MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_explicit D ε hk hε
      (directLdNaimarkStrategy D S) (directLdNaimarkStrategy_isProjective D S) hwin'
  exact directLdNaimarkStrategy_compress_soundness D S
    (_root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower
      ε D.q D.m D.d D.k) GA GB h1 h2 h3







end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLineGame/RoundedPolynomialEstimates.lean. -/
/-!
# Rounded extended-polynomial ordered estimates

Direct soundness retains all three consistency conclusions through compression.
Its same-space projective rounding supplies the point comparison used in both
ordered estimates, with the actual point and line errors retained.

## References

`eq:qld-g-42` and `eq:qld-g-43`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1300`.
The directly indexed completed-answer restriction is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ExtendedLineGame



/-- Undoing the joint coordinate equivalence recovers direct polynomial evaluation. -/
private theorem extendedPolynomialRead_equiv (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (u : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P u) =
      fun g => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u g (0 : Fin 1)) := by
  funext g
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead
  rw [Equiv.symm_apply_apply]



/-- Specialize projective refinement to the full polynomial-outcome norm sum. -/
private theorem ordered_error_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε} (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopposite : p1.IsOpposite p2)
    (R : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R) (eta : ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
      (fun x a => S.place p1 ((R.postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P x)).effect a))
      (fun x a => S.place p2
        ((points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat ≤ eta)
    (reverse : Bool) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S p1 p2 R reverse ≤ 4 * eta + 8 * δQ := by
  have h := points.ordered_dist_le p1 p2 hopposite R hR (_root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P)
    eta hpoint
  cases reverse
  · simpa only [_root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError, Bool.false_eq_true, if_false,
      mul_sub, mul_one, _root_.MIPStarRE.QPBT.opFamilyDistSq] using h.1
  · simpa only [_root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError, if_true,
      mul_sub, mul_one, _root_.MIPStarRE.QPBT.opFamilyDistSq] using h.2

/-- Reading the single scalar of an actual direct-game point answer recovers `Q`. -/
private theorem point_scalar_measurement {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δL : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε} {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness S points δL) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (u : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines side (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero P.extendedDirectLd)).postprocess
        (fun values => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (values (0 : Fin 1)))) =
      points.extendedQ side
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P u).1.1
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P u).1.2
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P u).2.1
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P u).2.2 := by
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv_apply]
  simp only [_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement, _root_.MIPStarRE.QPBT.directLdPointQuestionOf,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp,
    _root_.MIPStarRE.QPBT.ExtendedLineGame.pointAnswer, _root_.MIPStarRE.QPBT.directLdPointValuesOrZero, RingEquiv.apply_symm_apply]
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro a
  change (∑ b ∈ Finset.univ.filter (fun b : _root_.MIPStarRE.QPBT.PauliScalar P => b = a), _) = _
  classical
  erw [Finset.sum_filter, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

/-- Transport arbitrary POVM consistency to both heterogeneous expanded placements. -/
private theorem placed_consistency_pairState {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace .alice))
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace .bob)) :
    (_root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => S.place .AA' ((A x).effect a))
      (fun x a => S.place .BA'' ((B x).effect a)) S.psiHat =
      _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S)) ∧
    (_root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => S.place .BB' ((B x).effect a))
      (fun x a => S.place .AB'' ((A x).effect a)) S.psiHat =
      _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S)) := by
  have hA (x : X) (a : α) := (Matrix.nonneg_iff_posSemidef.mp ((A x).pos a)).isHermitian
  have hB (x : X) (a : α) := (Matrix.nonneg_iff_posSemidef.mp ((B x).pos a)).isHermitian
  constructor
  · unfold _root_.MIPStarRE.QPBT.consistencyDefect
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    split_ifs
    · rfl
    · simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm, _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
      exact (_root_.MIPStarRE.QPBT.ExtendedLineGame.stateQForm_pairState_eq_AA_prime_BA_prime_prime S _ _ (hA x a) (hB x b)).symm
  · unfold _root_.MIPStarRE.QPBT.consistencyDefect
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro x
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, Ne.symm hab, if_false, _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm,
        _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
      rw [S.place_comm .BB' .AB'' (by trivial)]
      exact (_root_.MIPStarRE.QPBT.ExtendedLineGame.stateQForm_pairState_eq_AB_prime_prime_BB_prime S _ _ (hA x a) (hB x b)).symm

set_option maxHeartbeats 800000 in
/-- Round concrete polynomial measurements satisfying the three direct
soundness bounds and transport them to the two ordered point comparisons. -/
private theorem rounded_polynomial_ordered_estimates_of_soundness
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δL : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ) (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness S points δL)
    (delta : ℝ)
    (A : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .alice))
    (B : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .bob))
    (hB : _root_.MIPStarRE.QPBT.consistencyDefect
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
        ((((_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).A
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)).postprocess
            (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero P.extendedDirectLd)).effect outcome) 1)
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
        ((B.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) ≤ delta)
    (hA : _root_.MIPStarRE.QPBT.consistencyDefect
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
        ((A.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
      (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
        ((((_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).B
          (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)).postprocess
            (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero P.extendedDirectLd)).effect outcome))
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) ≤ delta)
    (hAB : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (A.effect g) 1)
      (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (B.effect g)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) ≤ delta)
    (hdelta : 0 ≤ delta) :
    let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
      2 * Real.sqrt (2 * delta)
    ∃ RA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .alice),
    ∃ RB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .bob),
      _root_.MIPStarRE.QPBT.Measurement.IsProjective RA ∧ _root_.MIPStarRE.QPBT.Measurement.IsProjective RB ∧
      ∀ reverse : Bool,
        _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S .AA' .BA'' RA reverse ≤ 4 * eta + 8 * δQ ∧
        _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S .BB' .AB'' RB reverse ≤ 4 * eta + 8 * δQ := by
  classical
  intro eta
  obtain ⟨RA, RB, hRA, hRB, _, _, htransport⟩ :=
    _root_.MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState_norm S) A B delta hdelta hAB
  have hround := htransport
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) (fun u => _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)
  have hRApoint := hround.1
    (fun u => ((_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero P.extendedDirectLd)) delta hA
  have hRBpoint := hround.2
    (fun u => ((_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero P.extendedDirectLd)) delta hB
  rw [← two_mul delta] at hRApoint hRBpoint
  change _root_.MIPStarRE.QPBT.consistencyDefect _ _ _ _ ≤ eta at hRApoint hRBpoint
  have hAscalar := (_root_.MIPStarRE.QPBT.consistencyDefect_postprocess_question_le
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
    (fun u => RA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u))
    (fun u => ((_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero P.extendedDirectLd)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S)
    (fun _ values => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (values (0 : Fin 1)))).trans hRApoint
  have hBscalar := (_root_.MIPStarRE.QPBT.consistencyDefect_postprocess_question_le
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
    (fun u => ((_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf P.extendedDirectLd u)).postprocess
      (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero P.extendedDirectLd))
    (fun u => RB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S)
    (fun _ values => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (values (0 : Fin 1)))).trans hRBpoint
  change _root_.MIPStarRE.QPBT.consistencyDefect _ _ _ (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) ≤ eta at hAscalar hBscalar
  dsimp only [_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy] at hAscalar hBscalar
  conv at hAscalar =>
    lhs; arg 3; ext u c; arg 2; arg 1
    erw [point_scalar_measurement lines .bob u]
  conv at hBscalar =>
    lhs; arg 2; ext u c; arg 1; arg 1
    erw [point_scalar_measurement lines .alice u]
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp] at hAscalar hBscalar
  conv at hAscalar =>
    lhs; arg 2; ext u c; arg 1; arg 1
    rw [← extendedPolynomialRead_equiv P u]
  conv at hBscalar =>
    lhs; arg 3; ext u c; arg 2; arg 1
    rw [← extendedPolynomialRead_equiv P u]
  have hAquestion : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
      (fun x c => _root_.MIPStarRE.QPBT.heteroKron ((RA.postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P x)).effect c) 1)
      (fun x c => _root_.MIPStarRE.QPBT.heteroKron 1
        ((points.extendedQ .bob x.1.1 x.1.2 x.2.1 x.2.2).effect c)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) ≤ eta := by
    rw [← _root_.MIPStarRE.QPBT.consistencyDefect_uniform_question_equiv (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P)]
    exact hAscalar
  have hBquestion : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
      (fun x c => _root_.MIPStarRE.QPBT.heteroKron
        ((points.extendedQ .alice x.1.1 x.1.2 x.2.1 x.2.2).effect c) 1)
      (fun x c => _root_.MIPStarRE.QPBT.heteroKron 1 ((RB.postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P x)).effect c))
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) ≤ eta := by
    rw [← _root_.MIPStarRE.QPBT.consistencyDefect_uniform_question_equiv (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P)]
    exact hBscalar
  have hAplaced := (placed_consistency_pairState S
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
    (fun x => RA.postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P x))
    (fun x => points.extendedQ .bob x.1.1 x.1.2 x.2.1 x.2.2)).1.trans_le hAquestion
  have hBplaced := (placed_consistency_pairState S
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
    (fun x => points.extendedQ .alice x.1.1 x.1.2 x.2.1 x.2.2)
    (fun x => RB.postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P x))).2.trans_le hBquestion
  exact ⟨RA, RB, hRA, hRB, fun reverse =>
    ⟨ordered_error_le points .AA' .BA'' (by trivial) RA hRA eta hAplaced reverse,
      ordered_error_le points .BB' .AB'' (by trivial) RB hRB eta hBplaced reverse⟩⟩









end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Rounded extended-polynomial ordered estimates

Direct soundness retains all three consistency conclusions through compression.
Its same-space projective rounding supplies the point comparison used in both
ordered estimates, with the actual point and line errors retained.

## References

`eq:qld-g-42` and `eq:qld-g-43`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1300`.
The directly indexed completed-answer restriction is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



open MIPStarRE.QPBT.ExtendedLineGame

set_option maxHeartbeats 800000 in
-- The proof elaborates both ordered finite-sum estimates and their rounded witnesses.

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε δQ δL : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
        (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ) (_lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness S points δL),
      let delta := _root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower
        (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q))
        P.q (2 * P.m + 2) P.d 1
      let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
        2 * Real.sqrt (2 * delta)
      ∃ RA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .alice),
      ∃ RB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace .bob),
        _root_.MIPStarRE.QPBT.Measurement.IsProjective RA ∧ _root_.MIPStarRE.QPBT.Measurement.IsProjective RB ∧
        ∀ reverse : Bool,
          _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S .AA' .BA'' RA reverse ≤ 4 * eta + 8 * δQ ∧
          _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialOrderedError S .BB' .AB'' RB reverse ≤ 4 * eta + 8 * δQ := by
  classical
  let a := _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
  have ha : 1 ≤ a := by
    dsimp only [a, _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant]
    norm_num
  intro P ε δQ δL S points lines delta eta
  have hm := P.one_le_m
  have hd := P.hd
  have hq : 0 < P.q := by
    obtain ⟨k, _, hk⟩ := P.hq
    rw [hk]
    positivity
  have hpos : 0 < _root_.MIPStarRE.QPBT.directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q) :=
    _root_.MIPStarRE.QPBT.directPassingErrorEnvelope_pos _ _ (by positivity)
  obtain ⟨A, B, hB, hA, hAB⟩ :=
    _root_.MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_any_strategy_explicit P.extendedDirectLd _ rfl hpos
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy_value_ge_directPassingErrorEnvelope lines)
  change _root_.MIPStarRE.QPBT.consistencyDefect _ _ _ _ ≤ delta at hA hB hAB
  have hdelta : 0 ≤ delta := by
    dsimp [delta, _root_.MIPStarRE.QPBT.deltaLd]
    have ha0 : 0 ≤ a := le_trans (by norm_num) ha
    positivity
  exact rounded_polynomial_ordered_estimates_of_soundness
    S points lines delta A B hB hA hAB hdelta
