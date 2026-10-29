-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.exists_unit_residual
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:30:06.630417+00:00
-- url     : https://prove2.me/submissions/9fbb5d59-f225-4ab0-9c23-a5ebc07f5b72

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.exists_unit_residual.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_State

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/IdealTarget.lean. -/
/-!
# The ideal target of the Magic Square rigidity theorem

The conclusion of `thm:ms-rigidity` compares the two players' bit measurements
with the Pauli basis projectors on a two-qubit register and their shared state
with two EPR pairs tensored with an auxiliary bipartite state.  This file
records the two elementary properties of that target which the estimates of the
rigidity assembly use: the Pauli basis projectors of one kind form a complete
projective measurement, so that any marginal of them is a positive contraction,
and the ideal state is a unit vector whenever the auxiliary state is.

The completeness of the Pauli basis follows from the Fourier expansion
`tauObservable_eq_sum_pauliProj` evaluated at the zero label, where the
generalized Pauli observable is the identity.  Positivity is the rank-one
factorization `pauliProj W e = v vᴴ` for the normalized Pauli eigenvector `v`.

## References

`def:generalized-pauli` and blueprint
`lem:pauli-observable-expansion`, paper
`references/qpbt-paper/04_preliminaries.tex:908-1161`; the target of the
rigidity theorem is blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
/-! ## Marginals of the Pauli basis -/













/-! ## The ideal state is normalized -/

/-- The ideal state of `thm:ms-rigidity`, a maximally entangled state on the
extracted registers tensored with an auxiliary bipartite state and shuffled into
local player order, has the norm of the auxiliary state.  In particular it is a
unit vector whenever the auxiliary state is.  The norm identities for the
coordinate operations are `reindexState_norm_eq` and `vecTensor_norm_eq` in
`MIPStarRE/QPBT/State.lean`.  Blueprint `thm:ms-rigidity`. -/
theorem norm_reindexState_prodShuffle_vecTensor_eprState {V ιA'' ιB'' : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype ιA''] [DecidableEq ιA'']
    [Fintype ιB''] [DecidableEq ιB''] (aux : EuclideanSpace ℂ (ιA'' × ιB'')) :
    ‖_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) aux)‖ = ‖aux‖ := by
  rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq, _root_.MIPStarRE.QPBT.eprState_norm, one_mul]

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/JointState.lean. -/
/-!
# The joint state estimate of Magic Square rigidity

This file proves the state estimate of `thm:ms-rigidity` on the dilated
strategy: the tensor of the two players' two-qubit controlled-swap embeddings
carries the shared state to within `O(sqrt ε + sqrt δ)` of two EPR pairs
tensored with a residual bipartite vector, and that residual can be normalized
to the unit auxiliary state of the conclusion.

The argument is the coordinatewise one.  The image of the state under the two
embeddings has, at the pair of register labels `(e, f)`, the component

    `(A_e ⊗ B_f) ψ`,

where `A_e` and `B_f` are the residual factors of the two controlled swaps.
Since the two logical pairs are applied in succession, each component factors as
a second-pair component applied to a first-pair component, so the estimates of
`Rigidity/SwapPair.lean` apply twice: once on the state, once on the residual of
the first pair, whose second-pair hypotheses are supplied by
`Rigidity/SwapTransport.lean`.  Every component with `e ≠ f` is small and every
component with `e = f` is close to the one at the zero label; sixteen labels
then give the estimate.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

variable {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-! ## Coordinates -/







/-! ## The target state in coordinates -/





/-! ## From componentwise bounds to the joint estimate -/





/-! ## Residual factors -/









/-! ## The commutator of an anticommutator with a first-pair reflection -/



/-! ## The second-pair defects on the residual of the first swap -/



/-! ## The joint state estimate -/







/-! ## Normalizing the residual -/

/-- The coordinate tensor is homogeneous in its second argument. -/
theorem vecTensor_smul_right {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (c : ℂ) (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    _root_.MIPStarRE.QPBT.vecTensor u (c • v) = c • _root_.MIPStarRE.QPBT.vecTensor u v := by
  ext p
  simp [_root_.MIPStarRE.QPBT.vecTensor, EuclideanSpace.equiv]
  ring

/-- Reindexing is homogeneous. -/
theorem reindexState_smul {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (c : ℂ) (x : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.reindexState e (c • x) = c • _root_.MIPStarRE.QPBT.reindexState e x := by
  ext p
  simp [_root_.MIPStarRE.QPBT.reindexState, EuclideanSpace.equiv]



end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# The joint state estimate of Magic Square rigidity

This file proves the state estimate of `thm:ms-rigidity` on the dilated
strategy: the tensor of the two players' two-qubit controlled-swap embeddings
carries the shared state to within `O(sqrt ε + sqrt δ)` of two EPR pairs
tensored with a residual bipartite vector, and that residual can be normalized
to the unit auxiliary state of the conclusion.

The argument is the coordinatewise one.  The image of the state under the two
embeddings has, at the pair of register labels `(e, f)`, the component

    `(A_e ⊗ B_f) ψ`,

where `A_e` and `B_f` are the residual factors of the two controlled swaps.
Since the two logical pairs are applied in succession, each component factors as
a second-pair component applied to a first-pair component, so the estimates of
`Rigidity/SwapPair.lean` apply twice: once on the state, once on the residual of
the first pair, whose second-pair hypotheses are supplied by
`Rigidity/SwapTransport.lean`.  Every component with `e ≠ f` is small and every
component with `e = f` is close to the one at the zero label; sixteen labels
then give the estimate.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



variable {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-! ## Coordinates -/







/-! ## The target state in coordinates -/





/-! ## From componentwise bounds to the joint estimate -/





/-! ## Residual factors -/









/-! ## The commutator of an anticommutator with a first-pair reflection -/



/-! ## The second-pair defects on the residual of the first swap -/



variable {X₁A Z₁A X₂A Z₂A : _root_.LIDT.MIPStarRE.Quantum.Op ιA} {X₁B Z₁B X₂B Z₂B : _root_.LIDT.MIPStarRE.Quantum.Op ιB} {t : ℝ}







/-! ## The joint state estimate -/







/-! ## Normalizing the residual -/

theorem solution {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (u : EuclideanSpace ℂ ((V × ιA) × (V × ιB))) (hu : ‖u‖ = 1)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) (c : ℝ)
    (r0 : EuclideanSpace ℂ (ιA × ιB))
    (h : ‖u - _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r0)‖ ≤ c) :
    ∃ r : EuclideanSpace ℂ (ιA × ιB), ‖r‖ = 1 ∧
      ‖u - _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r)‖ ≤ 2 * c := by
  have htarget : ∀ r : EuclideanSpace ℂ (ιA × ιB),
      ‖_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r)‖ = ‖r‖ :=
    fun r => _root_.MIPStarRE.QPBT.norm_reindexState_prodShuffle_vecTensor_eprState r
  have hgap : |1 - ‖r0‖| ≤ c := by
    have h1 := abs_norm_sub_norm_le u
      (_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r0))
    rw [hu, htarget] at h1
    exact le_trans h1 h
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) hgap
  by_cases h0 : r0 = 0
  · refine ⟨ψ, hψ, ?_⟩
    have h1 : (1 : ℝ) ≤ c := by
      rw [h0, norm_zero] at hgap
      simpa using hgap
    calc ‖u - _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) ψ)‖
        ≤ ‖u‖ + ‖_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) ψ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hu, htarget, hψ]; norm_num
      _ ≤ 2 * c := by linarith
  · have hN : 0 < ‖r0‖ := norm_pos_iff.mpr h0
    refine ⟨((‖r0‖ : ℝ) : ℂ)⁻¹ • r0, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN,
        inv_mul_cancel₀ (ne_of_gt hN)]
    · have hscal : _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle
          (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) (((‖r0‖ : ℝ) : ℂ)⁻¹ • r0)) =
          ((‖r0‖ : ℝ) : ℂ)⁻¹ • _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r0) := by
        rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.vecTensor_smul_right, _root_.MIPStarRE.QPBT.MagicSquareRigidity.reindexState_smul]
      have hdiff : ‖_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r0) -
          _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle
            (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) (((‖r0‖ : ℝ) : ℂ)⁻¹ • r0))‖ = |1 - ‖r0‖| := by
        have hcollect : _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r0) -
            ((‖r0‖ : ℝ) : ℂ)⁻¹ •
              _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r0) =
            ((1 : ℂ) - ((‖r0‖ : ℝ) : ℂ)⁻¹) •
              _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r0) := by
          module
        have hs : ‖(1 : ℂ) - ((‖r0‖ : ℝ) : ℂ)⁻¹‖ = |1 - ‖r0‖⁻¹| := by
          rw [show (1 : ℂ) - ((‖r0‖ : ℝ) : ℂ)⁻¹ = (((1 - ‖r0‖⁻¹ : ℝ)) : ℂ) by
            push_cast
            ring]
          rw [Complex.norm_real, Real.norm_eq_abs]
        have hfin : |1 - ‖r0‖⁻¹| * ‖r0‖ = |1 - ‖r0‖| := by
          have h1 : (1 - ‖r0‖⁻¹) * ‖r0‖ = -(1 - ‖r0‖) := by
            field_simp
            ring
          calc |1 - ‖r0‖⁻¹| * ‖r0‖ = |1 - ‖r0‖⁻¹| * |‖r0‖| := by rw [abs_of_pos hN]
            _ = |(1 - ‖r0‖⁻¹) * ‖r0‖| := (abs_mul _ _).symm
            _ = |-(1 - ‖r0‖)| := by rw [h1]
            _ = |1 - ‖r0‖| := abs_neg _
        rw [hscal, hcollect, norm_smul, htarget, hs, hfin]
      have htri := norm_sub_le_norm_sub_add_norm_sub u
        (_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) r0))
        (_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState V) (((‖r0‖ : ℝ) : ℂ)⁻¹ • r0)))
      rw [hdiff] at htri
      linarith [htri, h, hgap]
