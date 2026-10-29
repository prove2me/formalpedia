-- Prove2me | solution 1 for MIPStarRE.QPBT.projective_rounding_with_explicit_constant
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:09:25.241413+00:00
-- url     : https://prove2.me/submissions/fd4e5dec-4929-44d1-8f3a-fda8b8567c78

-- Generated proof for MIPStarRE.QPBT.projective_rounding_with_explicit_constant.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_ProjectiveRounding
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Upstream
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_matrix_eq_zero_of_rank_eq_zero
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_projectiveLowRankSum
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_qxpProjSubMeas_total_eq_xHat_adjoint_mul_xHat
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_completion_self_distance
import Theorems.Thm_LIDT_MIPStarRE_LDT_PureState_ev_eq_re_inner
import Theorems.Thm_LIDT_MIPStarRE_LDT_PureState_toQuantumState_isNormalized
import Theorems.Thm_LIDT_MIPStarRE_LDT_qBipartiteConsDefect_of_measurements
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq

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
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

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
namespace MIPStarRE.LDT.MakingMeasurementsProjective
open LIDT.MIPStarRE.LDT
noncomputable section









/-- Left tensor placement is block diagonal with the same block at every
right index. -/
private lemma leftTensor_eq_blockDiagonal_const {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : _root_.LIDT.MIPStarRE.Quantum.Op ιA) :
    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) X = Matrix.blockDiagonal (fun _ : ιB => X) := by
  ext x y
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  by_cases h : b = c
  · subst c
    simp [_root_.LIDT.MIPStarRE.LDT.leftTensor, Matrix.blockDiagonal_apply]
  · simp [_root_.LIDT.MIPStarRE.LDT.leftTensor, Matrix.blockDiagonal_apply, h]

/-- The trace against a constant block-diagonal operator is the sum of the
traces of the diagonal blocks. -/
private lemma trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : _root_.LIDT.MIPStarRE.Quantum.Op ιA)
    (M : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) :
    Matrix.trace (Matrix.blockDiagonal (fun _ : ιB => X) * M) =
      ∑ b : ιB, Matrix.trace (X * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.diagBlock M b) := by
  classical
  let e : ((ιA × ιB) × ιA) ≃ (ιB × (ιA × ιA)) :=
    { toFun := fun x => (x.1.2, (x.1.1, x.2))
      invFun := fun x => ((x.2.1, x.1), x.2.2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  simpa [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.diagBlock, Matrix.trace, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ιB × (ιA × ιA) =>
      X y.2.1 y.2.2 * M (y.2.2, y.1) (y.2.1, y.1)))

/-- Evaluating a local operator against the left marginal agrees with
evaluating its left tensor placement against the bipartite density. -/
private lemma normalizedTrace_leftMarginalDensity_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) (X : _root_.LIDT.MIPStarRE.Quantum.Op ιA) :
    _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalDensity ρ * X) =
      _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (ρ * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) X) := by
  have hcard : ((Fintype.card ιB : _root_.LIDT.MIPStarRE.LDT.Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold _root_.LIDT.MIPStarRE.Quantum.normalizedTrace _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  have hswap :
      ∑ b : ιB, Matrix.trace (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.diagBlock ρ b * X) =
        ∑ b : ιB, Matrix.trace (X * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.diagBlock ρ b) := by
    refine Finset.sum_congr rfl ?_
    intro b _
    exact Matrix.trace_mul_comm _ _
  rw [hswap]
  rw [Matrix.trace_mul_comm]
  rw [leftTensor_eq_blockDiagonal_const]
  rw [trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock]
  simp [Fintype.card_prod]
  ring

/-- The complex normalized trace of a local operator is preserved by passage to
the left marginal. This formalization-only identity supports the marginal
reduction in the locality-preserving projectivization lemma and the
explicit-constant form of the orthonormalization lemma. -/
lemma normalizedTrace_leftMarginalState_density_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (X : _root_.LIDT.MIPStarRE.Quantum.Op ιA) :
    _root_.LIDT.MIPStarRE.Quantum.normalizedTrace ((_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalState ψ).density * X) =
      _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (ψ.density * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) X) := by
  simpa [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalState] using
    normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density) (X := X)

/-- The left marginal of a normalized bipartite state is normalized. This
formalization-only lemma supports the marginal reduction in the
locality-preserving projectivization lemma and the explicit-constant form of
the orthonormalization lemma. -/
lemma leftMarginalState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)} (hψ : ψ.IsNormalized) :
    (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalState ψ).IsNormalized := by
  unfold _root_.LIDT.MIPStarRE.LDT.QuantumState.IsNormalized
  have hnorm :
      _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalState ψ).density =
        _root_.LIDT.MIPStarRE.Quantum.normalizedTrace ψ.density := by
    simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor_one] using
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.normalizedTrace_leftMarginalState_density_mul_eq (ψ := ψ)
        (X := (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA))
  exact hnorm.trans hψ

/-- Local evaluation in the left marginal equals bipartite evaluation of the
left tensor placement. This formalization-only identity supports the marginal
reduction in the locality-preserving projectivization lemma and the
explicit-constant form of the orthonormalization lemma. -/
lemma leftMarginal_ev_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (X : _root_.LIDT.MIPStarRE.Quantum.Op ιA) :
    _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) X) = _root_.LIDT.MIPStarRE.LDT.ev (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalState ψ) X := by
  simpa [_root_.LIDT.MIPStarRE.LDT.ev] using congrArg Complex.re
    (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.normalizedTrace_leftMarginalState_density_mul_eq (ψ := ψ) (X := X)).symm



end
end MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT

/- Source helpers from QPBT/Games/DistanceTheorems/ProjectiveRounding.lean. -/
/-!
# Projective rounding for consistent POVMs

This module proves the orthonormalization lemma `lem:ortho` with an explicit
error constant: if a POVM `Q` on Alice's space and a POVM `R` on Bob's space are
`δ`-consistent on a unit bipartite state `ψ`, then Alice has a projective
measurement `P` on her original space with `P_a ⊗ 1` within `220 · δ^(1/4)` of
`Q_a ⊗ 1` on `ψ`.

The argument passes to Alice's reduced state and follows the construction of the
LDT orthonormalization theorem. Rounding the almost-projective effects of `Q` and
reducing their ranks gives a family of projectors `Q_a` whose ranges are almost
orthogonal; assembling those ranges into one auxiliary space gives an operator
`X`, whose positive-Gram polar factor `X̂` is a coisometry; and pulling the block
projector of each outcome back along `X̂`, so that `P_a = X̂ᴴ T_a X̂`, gives a
projective family close to `Q`. The family `P` lives on Alice's original space
and is completed to a measurement at one fixed outcome once its missing state
mass has been shown to be small.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:131-153`
- Blueprint `lem:ortho`
- Blueprint `lem:ortho-explicit-constant`, the statement proved in this module
- `references/ldt-paper/orthonormalization.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section



/-- The QPBT vector quadratic form equals evaluation in `roundPureState`. -/
private theorem round_stateQForm_eq_ev {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (T : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ T = _root_.LIDT.MIPStarRE.LDT.ev (roundPureState ψ hψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) T := by
  rw [_root_.LIDT.MIPStarRE.LDT.PureState.ev_eq_re_inner]
  simp only [roundPureState]
  change (inner ℂ ψ (WithLp.toLp 2 (T *ᵥ ψ.ofLp))).re =
    (star ψ.ofLp ⬝ᵥ T *ᵥ ψ.ofLp).re
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- Evaluation of an operator square in `roundPureState` is the squared vector norm. -/
private theorem round_ev_adjoint_mul_self_eq_norm_sq {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (T : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.ev (roundPureState ψ hψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) (Tᴴ * T) =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState T ψ‖ ^ 2 := by
  rw [← round_stateQForm_eq_ev]
  symm
  rw [@norm_sq_eq_re_inner ℂ]
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [_root_.LIDT.Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin T ψ) (Matrix.toEuclideanLin T ψ)).re =
    (inner ℂ ψ ((Matrix.toEuclideanLin T).adjoint (Matrix.toEuclideanLin T ψ))).re
  rw [LinearMap.adjoint_inner_right]



/-- A complete measurement on a nonzero finite space has a nonempty outcome type. -/
private theorem round_measurement_outcome_nonempty {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) : Nonempty α := by
  classical
  by_contra hα
  haveI : IsEmpty α := not_nonempty_iff.mp hα
  let i : ι := Classical.choice inferInstance
  have heq := congrArg (fun X : _root_.LIDT.MIPStarRE.Quantum.Op ι => X i i) M.sum_eq_one
  simp [Matrix.sum_apply] at heq

/-- QPBT vector consistency is the LDT bipartite consistency relation on the
associated pure state and concrete measurements. -/
private lemma round_consRel_of_consistencyDefect {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α] [Nonempty ιA] [Nonempty ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (Q : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA)
    (R : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (δ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hcons : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (R.effect a)) ψ ≤ δ) :
    let ψp : _root_.LIDT.MIPStarRE.LDT.PureState (ιA × ιB) := roundPureState ψ hψ
    let HA : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace := roundFiniteHilbertSpace ιA
    let HB : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace := roundFiniteHilbertSpace ιB
    let A : _root_.LIDT.MIPStarRE.LDT.Measurement α ιA :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement (H := HA) Q
    let B : _root_.LIDT.MIPStarRE.LDT.Measurement α ιB :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement (H := HB) R
    _root_.LIDT.MIPStarRE.LDT.ConsRel (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily A.toSubMeas) (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B.toSubMeas) δ := by
    dsimp
    let Qm : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement α (roundFiniteHilbertSpace ιA) := Q
    let Rm : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement α (roundFiniteHilbertSpace ιB) := R
    constructor
    change _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
        (roundPureState ψ hψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement Qm).toSubMeas)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement Rm).toSubMeas) ≤ δ
    rw [show _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
        (roundPureState ψ hψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement Qm).toSubMeas)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement Rm).toSubMeas) =
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect
          (roundPureState ψ hψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement Qm).toSubMeas
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement Rm).toSubMeas by
      simp [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError, _root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, _root_.LIDT.MIPStarRE.LDT.constSubMeasFamily]]
    rw [_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_of_measurements]
    rw [_root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized _ (roundPureState ψ hψ).toQuantumState_isNormalized]
    rw [show _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass (roundPureState ψ hψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement Qm).toSubMeas
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement Rm).toSubMeas =
      ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (Q.effect a) (R.effect a)) by
      unfold _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass
      apply Finset.sum_congr rfl
      intro a _
      simpa [Qm, Rm, MatrixMeasurement.toMeasurement_outcome,
        _root_.MIPStarRE.QPBT.heteroKron, _root_.LIDT.MIPStarRE.LDT.opTensor] using
        (round_stateQForm_eq_ev ψ hψ (_root_.MIPStarRE.QPBT.heteroKron (Q.effect a) (R.effect a))).symm]
    have hpoint := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
      (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιB) Q)
      (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιA) R) ψ
    have hdefect : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (R.effect a)) ψ =
        1 - ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (Q.effect a) (R.effect a)) := by
      unfold _root_.MIPStarRE.QPBT.consistencyDefect
      simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
      rw [show _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (fun _ => ∑ a : α, ∑ b : α, if a = b then 0 else
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
              (_root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron 1 (R.effect b))) =
          ∑ a : α, ∑ b : α, if a = b then 0 else
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
              (_root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron 1 (R.effect b)) by
        simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution]]
      rw [show (∑ a : α, ∑ b : α, if a = b then 0 else
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
              (_root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron 1 (R.effect b))) =
          ‖ψ‖ ^ 2 - ∑ a : α,
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (Q.effect a) (R.effect a)) by
        have hdiag :
            (∑ a : α,
                _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (Q.effect a) (R.effect a))) =
              ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
                ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιB) Q).effect a *
                  (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιA) R).effect a) := by
          apply Finset.sum_congr rfl
          intro a _
          symm
          simpa [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement,
            _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
            _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] using
              _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq ψ (Q.effect a) (R.effect a)
        rw [hdiag]
        simpa [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement,
          _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
          _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] using hpoint]
      rw [hψ]
      norm_num
    rw [← hdefect]
    exact hcons

/-- Rank reduction of the almost-projective effects, orthonormalization of the
resulting ranges into the family `P_a = X̂ᴴ T_a X̂`, and completion at one fixed
outcome give a projective measurement on Alice's original space within
`220 * δ^(1/4)` of the given one. -/
private lemma round_projective_ldt {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α] [Nonempty ιA] [Nonempty ιB]
    (Ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (hΨ : Ψ.IsNormalized)
    (A : _root_.LIDT.MIPStarRE.LDT.Measurement α ιA)
    (B : _root_.LIDT.MIPStarRE.LDT.Measurement α ιB) (a₀ : α) (δ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hδ : 0 ≤ δ)
    (hCons : _root_.LIDT.MIPStarRE.LDT.ConsRel Ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily A.toSubMeas) (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B.toSubMeas) δ) :
    ∃ C : _root_.LIDT.MIPStarRE.LDT.ProjMeas α ιA,
      _root_.LIDT.MIPStarRE.LDT.qSDD Ψ (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) C.toSubMeas) ≤
          220 * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot δ := by
  classical
  let φ : _root_.LIDT.MIPStarRE.LDT.QuantumState ιA := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalState Ψ
  have hφ : φ.IsNormalized := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalState_isNormalized hΨ
  let t : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot δ
  have ht_nonneg : 0 ≤ t := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot_nonneg hδ
  by_cases ht_small : t ≤ 1 / (24 : _root_.LIDT.MIPStarRE.LDT.Error)
  · have hδ_small : δ ≤ 1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error) := by
      have ht_four : t ^ (4 : Nat) = δ := by
        dsimp [t, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot]
        calc
          (Real.rpow δ (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (4 : Nat) =
              Real.rpow δ ((1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) * 4) := by
                rw [← Real.rpow_natCast]
                simpa using
                  (Real.rpow_mul hδ (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) (4 : _root_.LIDT.MIPStarRE.LDT.Error)).symm
          _ = δ := by norm_num [Real.rpow_natCast]
      have hpow := pow_le_pow_left₀ ht_nonneg ht_small 4
      rw [ht_four] at hpow
      calc
        δ ≤ (1 / (24 : _root_.LIDT.MIPStarRE.LDT.Error)) ^ (4 : Nat) := hpow
        _ ≤ 1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
    have hAlmost := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
      (ψ := Ψ) (A := A) (B := B) (ζ := δ) hCons
    have hsourceLifted := hAlmost.sourceAlmostProjective
    have hterm : ∀ a : α,
        _root_.LIDT.MIPStarRE.LDT.ev Ψ
          ((_root_.LIDT.MIPStarRE.LDT.leftLiftedMeasurement (ιB := ιB) A).outcome a -
            (_root_.LIDT.MIPStarRE.LDT.leftLiftedMeasurement (ιB := ιB) A).outcome a *
              (_root_.LIDT.MIPStarRE.LDT.leftLiftedMeasurement (ιB := ιB) A).outcome a) =
        _root_.LIDT.MIPStarRE.LDT.ev φ (A.outcome a - A.outcome a * A.outcome a) := by
      intro a
      simpa [φ, _root_.LIDT.MIPStarRE.LDT.leftLiftedMeasurement, _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.leftTensor_sub,
        _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor] using
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginal_ev_eq Ψ (A.outcome a - A.outcome a * A.outcome a))
    have hsource :
        ∑ a, _root_.LIDT.MIPStarRE.LDT.ev φ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * δ := by
      simpa [hterm, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjectiveError] using hsourceLifted
    obtain ⟨qLayer, hRank⟩ :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.projectiveLowRankSum φ A δ hφ hδ hδ_small hsource
    have hq_complete :
        _root_.LIDT.MIPStarRE.LDT.ev φ (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal qLayer) ≥ 1 - 11 * t := by
      simpa [t] using _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qCompleteness φ A δ qLayer hφ hδ hδ_small hRank
    have hsigma : Nonempty (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.sigmaFinCarrier
        (fun a : α => (qLayer.q.outcome a).rank)) := by
      by_contra hsigma
      have hzero_rank : ∀ a : α, (qLayer.q.outcome a).rank = 0 := by
        intro a
        by_contra hrank
        have hpos : 0 < (qLayer.q.outcome a).rank := Nat.pos_of_ne_zero hrank
        have : Nonempty (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.sigmaFinCarrier
            (fun a : α => (qLayer.q.outcome a).rank)) := by
          refine ⟨⟨Fintype.equivFin α a, ⟨0, ?_⟩⟩⟩
          simpa [Fintype.equivFin] using hpos
        exact hsigma this
      have hzero : ∀ a : α, qLayer.q.outcome a = 0 := by
        intro a
        exact _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.matrix_eq_zero_of_rank_eq_zero
          (qLayer.q.outcome a) (hzero_rank a)
      have htotal_zero : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal qLayer = 0 := by
        calc
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal qLayer = ∑ a, qLayer.q.outcome a := hRank.sum_eq_total.symm
          _ = 0 := Finset.sum_eq_zero fun a _ => hzero a
      have : _root_.LIDT.MIPStarRE.LDT.ev φ (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal qLayer) = 0 := by simp [htotal_zero, _root_.LIDT.MIPStarRE.LDT.ev]
      rw [this] at hq_complete
      nlinarith
    letI := hsigma
    obtain ⟨_xHat, _hxHat_coisometry, _hxHat_mixed, data, hq, _hx, _hxHat, hQP⟩ :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.pQApprox_ofRankReductionSigmaRangePositiveGram φ A δ hRank hφ hδ hδ_small
    have hRankData : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.RankReductionWitness φ A δ data.qLayer := by
      exact hq.symm ▸ hRank.toSigmaRangeQLayer
    have hAQ :
        _root_.LIDT.MIPStarRE.LDT.SDDOpRel φ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (A.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily α ιA))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily data.qLayer.q) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.roundingToProjectiveError δ) := by
      simpa [hq] using hRank.toSigmaRangeQLayer.closeness
    have hAP :
        _root_.LIDT.MIPStarRE.LDT.SDDOpRel φ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (A.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily α ιA))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data)) (84 * t) := by
      have htri := _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_triangle φ
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (A.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily α ιA))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily data.qLayer.q) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.roundingToProjectiveError δ) (30 * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot δ) hAQ hQP
      refine _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_mono φ
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (A.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily α ιA))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data))
        (2 * (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.roundingToProjectiveError δ + 30 * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot δ))
        (84 * t) htri ?_
      have htrunc : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationError δ ≤ _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot δ :=
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationError_le_zetaQuarterRoot δ hδ hδ_small
      dsimp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.roundingToProjectiveError, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationError, t]
      dsimp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationError] at htrunc
      nlinarith
    let P : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas α ιA := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qxpProjSubMeas data
    let pMass : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.ev φ P.toSubMeas.total
    let qMass : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.ev φ (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer)
    let sqrtMass : _root_.LIDT.MIPStarRE.LDT.Error := _root_.LIDT.MIPStarRE.LDT.ev φ (CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer))
    have hqtotal_nonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer := by
      rw [← hRankData.sum_eq_total]
      exact Finset.sum_nonneg fun a _ => hRankData.outcome_nonneg a
    have hq_nonneg : 0 ≤ qMass := by
      dsimp [qMass]
      exact _root_.LIDT.MIPStarRE.LDT.ev_nonneg_of_psd φ _ hqtotal_nonneg
    have hp_nonneg : 0 ≤ pMass := by
      exact _root_.LIDT.MIPStarRE.LDT.ev_nonneg_of_psd φ P.toSubMeas.total P.toSubMeas.total_nonneg
    have hp_le_one : pMass ≤ 1 := by
      calc
        pMass ≤ _root_.LIDT.MIPStarRE.LDT.ev φ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) :=
          _root_.LIDT.MIPStarRE.LDT.ev_mono φ _ _ P.toSubMeas.total_le_one
        _ = 1 := _root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized φ hφ
    have hsqrt_nonneg : 0 ≤ sqrtMass := by
      exact _root_.LIDT.MIPStarRE.LDT.ev_nonneg_of_psd φ _ (CFC.sqrt_nonneg (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer))
    have hsqrt_complete : sqrtMass ≥ 1 - 12 * t := by
      simpa [sqrtMass, t] using
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.sqrtQCompleteness φ A δ data.qLayer hφ hδ hδ_small hRankData
    have hsupport :
        CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer) * P.toSubMeas.total =
          CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer) := by
      rw [show P.toSubMeas.total = data.xHatᴴ * data.xHat by
        exact _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qxpProjSubMeas_total_eq_xHat_adjoint_mul_xHat data]
      rw [← data.xHat_mixed]
      calc
        data.xᴴ * data.xHat * (data.xHatᴴ * data.xHat) =
            data.xᴴ * (data.xHat * data.xHatᴴ) * data.xHat := by
              simp only [Matrix.mul_assoc]
        _ = data.xᴴ * data.xHat := by simp [data.xHat_coisometry]
    have hq_sqrt_sq :
        CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer) * (CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer))ᴴ =
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer := by
      have hsqrt_herm : (CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer))ᴴ =
          CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer) :=
        (Matrix.nonneg_iff_posSemidef.mp
          (CFC.sqrt_nonneg (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer))).isHermitian.eq
      calc
        CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer) * (CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer))ᴴ =
            CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer) * CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer) := by
              rw [hsqrt_herm]
        _ = _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer :=
          CFC.sqrt_mul_sqrt_self _ hqtotal_nonneg
    have hp_sq : P.toSubMeas.totalᴴ * P.toSubMeas.total =
        P.toSubMeas.total := by
      rw [(Matrix.nonneg_iff_posSemidef.mp P.toSubMeas.total_nonneg).isHermitian.eq]
      exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
    have hcs : |sqrtMass| ≤ Real.sqrt qMass * Real.sqrt pMass := by
      have hcs0 :=
        _root_.LIDT.MIPStarRE.LDT.ev_abs_mul_le_sqrt φ (CFC.sqrt (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QTotal data.qLayer)) P.toSubMeas.total
      rw [hsupport, hq_sqrt_sq, hp_sq] at hcs0
      simpa [sqrtMass, qMass, pMass] using hcs0
    have hsquare : sqrtMass ^ 2 ≤ qMass * pMass := by
      have hsquare' : |sqrtMass| ^ 2 ≤
          (Real.sqrt qMass * Real.sqrt pMass) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg sqrtMass)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hcs
      simpa [sq_abs, mul_pow, Real.sq_sqrt hq_nonneg,
        Real.sq_sqrt hp_nonneg] using hsquare'
    have hq_le : qMass ≤ 1 + 2 * t := by
      have hbound := _root_.LIDT.MIPStarRE.LDT.ev_mono φ _ _ hRankData.total_le
      have hbound' : qMass ≤ 1 + 2 * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationError δ := by
        have hscale :=
          _root_.LIDT.MIPStarRE.LDT.ev_scale φ (1 + 2 * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationError δ) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA)
        rw [_root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized φ hφ, mul_one] at hscale
        have hscalar :
            (((1 : _root_.LIDT.MIPStarRE.LDT.Error) + 2 * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationError δ : _root_.LIDT.MIPStarRE.LDT.Error) : ℂ) =
              (1 : ℂ) + 2 * (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationError δ : ℂ) := by
          norm_num
        rw [hscalar] at hscale
        dsimp [qMass]
        exact hbound.trans_eq hscale
      have htrunc := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationError_le_zetaQuarterRoot δ hδ hδ_small
      dsimp [t]
      linarith
    have hbase_nonneg : 0 ≤ 1 - 12 * t := by linarith
    have hbase_sq : (1 - 12 * t) ^ 2 ≤ sqrtMass ^ 2 :=
      (sq_le_sq₀ hbase_nonneg hsqrt_nonneg).2 hsqrt_complete
    have hqpmass : qMass * pMass ≤ (1 + 2 * t) * pMass :=
      mul_le_mul_of_nonneg_right hq_le hp_nonneg
    have hp_lower : 1 - 26 * t ≤ pMass := by
      nlinarith [sq_nonneg t]
    have hresidual :
        _root_.LIDT.MIPStarRE.LDT.ev φ ((1 - P.toSubMeas.total) * (1 - P.toSubMeas.total)) ≤ 26 * t := by
      have hresidual_eq :
          (1 - P.toSubMeas.total) * (1 - P.toSubMeas.total) =
            1 - P.toSubMeas.total := by
        calc
          (1 - P.toSubMeas.total) * (1 - P.toSubMeas.total) =
              1 - P.toSubMeas.total - P.toSubMeas.total +
                P.toSubMeas.total * P.toSubMeas.total := by noncomm_ring
          _ = 1 - P.toSubMeas.total := by
            rw [_root_.LIDT.MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P]
            abel
      rw [hresidual_eq, _root_.LIDT.MIPStarRE.LDT.ev_sub, _root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized φ hφ]
      dsimp [pMass] at hp_lower
      linarith
    let C : _root_.LIDT.MIPStarRE.LDT.ProjMeas α ιA :=
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj P a₀
    have hAPq : _root_.LIDT.MIPStarRE.LDT.qSDD φ A.toSubMeas P.toSubMeas ≤ 84 * t := by
      have hraw : _root_.LIDT.MIPStarRE.LDT.qSDDCore φ A.outcome (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data).outcome ≤ 84 * t := by
        simpa [_root_.LIDT.MIPStarRE.LDT.SDDOpRel, _root_.LIDT.MIPStarRE.LDT.sddErrorOp, _root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution,
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily, _root_.LIDT.MIPStarRE.LDT.qSDDOp, _root_.LIDT.MIPStarRE.LDT.SubMeas.toOpFamily] using hAP.squaredDistanceBound
      unfold _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
      unfold _root_.LIDT.MIPStarRE.LDT.qSDDCore at hraw
      simpa [P, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily, pFamilyFromXHat, Pa, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qxpProjSubMeas_outcome] using hraw
    have hPCq : _root_.LIDT.MIPStarRE.LDT.qSDD φ P.toSubMeas C.toSubMeas ≤ 26 * t := by
      rw [show C.toSubMeas =
          (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome P.toSubMeas a₀).toSubMeas by
        rfl]
      rw [_root_.LIDT.MIPStarRE.LDT.Preliminaries.completion_self_distance]
      exact hresidual
    have hACq : _root_.LIDT.MIPStarRE.LDT.qSDD φ A.toSubMeas C.toSubMeas ≤ 220 * t := by
      calc
        _root_.LIDT.MIPStarRE.LDT.qSDD φ A.toSubMeas C.toSubMeas ≤
            2 * (_root_.LIDT.MIPStarRE.LDT.qSDD φ A.toSubMeas P.toSubMeas +
              _root_.LIDT.MIPStarRE.LDT.qSDD φ P.toSubMeas C.toSubMeas) :=
          _root_.LIDT.MIPStarRE.LDT.Preliminaries.questionSDD_triangle
            φ A.toSubMeas P.toSubMeas C.toSubMeas
        _ ≤ 2 * (84 * t + 26 * t) := by gcongr
        _ = 220 * t := by ring
    refine ⟨C, ?_⟩
    have hlift :
        _root_.LIDT.MIPStarRE.LDT.qSDD Ψ (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) C.toSubMeas) =
        _root_.LIDT.MIPStarRE.LDT.qSDD φ A.toSubMeas C.toSubMeas := by
      unfold _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
      apply Finset.sum_congr rfl
      intro a _
      simpa [φ, _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.leftTensor_sub, _root_.LIDT.MIPStarRE.LDT.leftTensor_conjTranspose,
        _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor] using
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginal_ev_eq Ψ
          ((A.outcome a - C.outcome a)ᴴ * (A.outcome a - C.outcome a))
    rw [hlift]
    exact hACq
  · -- Outside the small-error range, the universal distance bound is below `220 * t`.
    let Z : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas α ιA := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas
    let C : _root_.LIDT.MIPStarRE.LDT.ProjMeas α ιA :=
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj Z a₀
    have hAZ :
        _root_.LIDT.MIPStarRE.LDT.qSDD Ψ (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Z.toSubMeas) ≤ 1 :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ A.toSubMeas
    have hCZ :
        _root_.LIDT.MIPStarRE.LDT.qSDD Ψ (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) C.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Z.toSubMeas) ≤ 1 :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ C.toSubMeas
    have hZC :
        _root_.LIDT.MIPStarRE.LDT.qSDD Ψ (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Z.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) C.toSubMeas) ≤ 1 := by
      simpa [_root_.LIDT.MIPStarRE.LDT.Preliminaries.qSDD_symm] using hCZ
    refine ⟨C, ?_⟩
    calc
      _root_.LIDT.MIPStarRE.LDT.qSDD Ψ (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) C.toSubMeas) ≤
          2 * (_root_.LIDT.MIPStarRE.LDT.qSDD Ψ (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
              (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Z.toSubMeas) +
            _root_.LIDT.MIPStarRE.LDT.qSDD Ψ (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Z.toSubMeas)
              (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) C.toSubMeas)) :=
        _root_.LIDT.MIPStarRE.LDT.Preliminaries.questionSDD_triangle Ψ
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Z.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) C.toSubMeas)
      _ ≤ 4 := by linarith
      _ ≤ 220 * t := by nlinarith



end

end MIPStarRE.QPBT

/-!
# Projective rounding for consistent POVMs

This module proves the orthonormalization lemma `lem:ortho` with an explicit
error constant: if a POVM `Q` on Alice's space and a POVM `R` on Bob's space are
`δ`-consistent on a unit bipartite state `ψ`, then Alice has a projective
measurement `P` on her original space with `P_a ⊗ 1` within `220 · δ^(1/4)` of
`Q_a ⊗ 1` on `ψ`.

The argument passes to Alice's reduced state and follows the construction of the
LDT orthonormalization theorem. Rounding the almost-projective effects of `Q` and
reducing their ranks gives a family of projectors `Q_a` whose ranges are almost
orthogonal; assembling those ranges into one auxiliary space gives an operator
`X`, whose positive-Gram polar factor `X̂` is a coisometry; and pulling the block
projector of each outcome back along `X̂`, so that `P_a = X̂ᴴ T_a X̂`, gives a
projective family close to `Q`. The family `P` lives on Alice's original space
and is completed to a measurement at one fixed outcome once its missing state
mass has been shown to be small.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:131-153`
- Blueprint `lem:ortho`
- Blueprint `lem:ortho-explicit-constant`, the statement proved in this module
- `references/ldt-paper/orthonormalization.tex`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (Q : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA)
    (R : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (δ : _root_.LIDT.MIPStarRE.LDT.Error) (hδ : 0 ≤ δ)
    (hcons : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (R.effect a)) ψ ≤ δ) :
    ∃ Pm : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA,
      _root_.MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (Pm.effect a) 1)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1) ψ ≤
          220 * Real.rpow δ (1 / 4 : _root_.LIDT.MIPStarRE.LDT.Error) := by
  have hι : Nonempty (ιA × ιB) := by
    by_contra hempty
    letI : IsEmpty (ιA × ιB) := not_nonempty_iff.mp hempty
    have hzero : ψ = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero] at hψ
    norm_num at hψ
  haveI : Nonempty ιA := ⟨(Classical.choice hι).1⟩
  haveI : Nonempty ιB := ⟨(Classical.choice hι).2⟩
  have hα : Nonempty α := round_measurement_outcome_nonempty Q
  letI : Nonempty α := hα
  let a₀ : α := Classical.choice hα
  let Ψ : _root_.LIDT.MIPStarRE.LDT.PureState (ιA × ιB) := roundPureState ψ hψ
  let HA : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace := roundFiniteHilbertSpace ιA
  let HB : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace := roundFiniteHilbertSpace ιB
  let A : _root_.LIDT.MIPStarRE.LDT.Measurement α ιA :=
    _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement (H := HA) Q
  let B : _root_.LIDT.MIPStarRE.LDT.Measurement α ιB :=
    _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement (H := HB) R
  have hCons : _root_.LIDT.MIPStarRE.LDT.ConsRel (Ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily A.toSubMeas) (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B.toSubMeas) δ := by
    simpa [Ψ, HA, HB, A, B] using
      round_consRel_of_consistencyDefect ψ hψ Q R δ hcons
  obtain ⟨C, hC⟩ := round_projective_ldt (Ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    Ψ.toQuantumState_isNormalized A B a₀ δ hδ hCons
  let Pm : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA :=
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne C.outcome C.outcome_pos <| by
      rw [C.sum_eq_total, C.total_eq_one]
  have hPm_projective : _root_.MIPStarRE.QPBT.Measurement.IsProjective Pm := by
    intro a
    change _root_.LIDT.MIPStarRE.Quantum.IsProj (C.outcome a)
    exact
      { isIdempotentElem := C.proj a
        isSelfAdjoint :=
          (Matrix.nonneg_iff_posSemidef.mp (C.outcome_pos a)).isHermitian.eq }
  refine ⟨Pm, hPm_projective, ?_⟩
  have hdist :
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (Pm.effect a) 1)
          (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1) ψ =
        _root_.LIDT.MIPStarRE.LDT.qSDD (Ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) C.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) A.toSubMeas) := by
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    rw [show _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ => ∑ a : α,
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.heteroKron (Pm.effect a) 1 - _root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1) ψ‖ ^ 2) =
        ∑ a : α,
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.heteroKron (Pm.effect a) 1 - _root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1) ψ‖ ^ 2 by
      simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution]]
    unfold _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
    apply Finset.sum_congr rfl
    intro a _
    rw [round_ev_adjoint_mul_self_eq_norm_sq ψ hψ]
    simp only [Pm, A, HA, _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas, mkLeftPlacedSubMeas_outcome,
      MatrixMeasurement.toMeasurement_outcome,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne]
    rfl
  rw [hdist]
  rw [_root_.LIDT.MIPStarRE.LDT.Preliminaries.qSDD_symm]
  simpa [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot] using hC
