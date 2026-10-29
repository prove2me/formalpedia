-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.isProj_sum_of_isProj_of_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:11:49.135152+00:00
-- url     : https://prove2.me/submissions/cb161e95-e799-49bd-ba1f-dd84d707499b

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.isProj_sum_of_isProj_of_sum_le_one.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_mul_eq_zero_of_isProj_of_add_le_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Dilation.lean. -/
/-!
# A simultaneous projective dilation of a Magic Square strategy

The rigidity argument for the Magic Square game is stated for an arbitrary
tensor-product strategy, whose measurements are positive operator valued
measures.  The self-testing argument, however, manipulates projections.  This
file removes that discrepancy by dilating an arbitrary strategy to a projective
one without changing any observable quantity.

Each local Hilbert space `ℂ^ι` is enlarged by one auxiliary register whose
basis is indexed by `Option MsAnswer`, and the original space is identified with
the *ground slice* `ℂ^ι ⊗ |⊥⟩`.  The one-measurement Naimark lemma of the low
individual degree development supplies, for every question separately, a family
of projections on the enlarged space whose compression to the ground slice
returns the original effects; the ancilla is the same for all questions, so the
identification of `ℂ^ι` with the ground slice is a single isometry serving every
question at once.  Folding the deficiency `1 - ∑_a P_a` into one distinguished
answer turns the dilated family into a complete projective measurement without
disturbing the compression, because the original effects already sum to the
identity.

Since the dilated state is the image of the original state under the two ground
embeddings, every Born probability, and hence the game value and all the
rejection, malformed-answer, cell-consistency and parity masses of the
value-to-parity layer, is unchanged.  Conversely, the local isometries produced
by a rigidity argument applied to the dilated strategy compose with the ground
embeddings to give local isometries of the original strategy, and the
state-dependent norms occurring in the conclusion of `thm:ms-rigidity` transfer
along that composition.

## References

The rigidity statement supported here is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, Theorem 6.9.  The dilation reuses the
one-measurement Naimark lemma of
`references/ldt-paper/orthonormalization.tex:121-159`, formalized as
`MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-! ## Orthogonality inside a subnormalized family of projections -/



/-- Formalization-only auxiliary lemma for the dilation of `thm:ms-rigidity`
(blueprint `thm:ms-rigidity`).  A finite family of orthogonal
projections whose sum is at most the identity is mutually orthogonal: for two
distinct indices the two projections already sum to at most the identity, so the
previous lemma applies. -/
theorem mul_eq_zero_of_isProj_family {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] {P : α → _root_.LIDT.MIPStarRE.Quantum.Op d} (hP : ∀ a, _root_.LIDT.MIPStarRE.Quantum.IsProj (P a))
    (hsum : ∑ a, P a ≤ 1) {a b : α} (hab : a ≠ b) :
    P a * P b = 0 := by
  classical
  refine _root_.MIPStarRE.QPBT.MagicSquareRigidity.mul_eq_zero_of_isProj_of_add_le_one (hP a) (hP b).nonneg ?_
  refine le_trans ?_ hsum
  have hpair : ∑ c ∈ ({a, b} : Finset α), P c = P a + P b := by
    rw [Finset.sum_pair hab]
  rw [← hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun c _ _ => (hP c).nonneg)



/-! ## The ground slice of an enlarged local space -/



























/-! ## The dilated projective measurement -/

























/-! ## The dilated state -/













/-! ## The dilated Magic Square strategy -/













/-! ## Preservation of the value-to-parity layer -/



































/-! ## Composition of the dilation with later local isometries -/



















/-! ## Transfer of state-dependent bounds -/

















end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# A simultaneous projective dilation of a Magic Square strategy

The rigidity argument for the Magic Square game is stated for an arbitrary
tensor-product strategy, whose measurements are positive operator valued
measures.  The self-testing argument, however, manipulates projections.  This
file removes that discrepancy by dilating an arbitrary strategy to a projective
one without changing any observable quantity.

Each local Hilbert space `ℂ^ι` is enlarged by one auxiliary register whose
basis is indexed by `Option MsAnswer`, and the original space is identified with
the *ground slice* `ℂ^ι ⊗ |⊥⟩`.  The one-measurement Naimark lemma of the low
individual degree development supplies, for every question separately, a family
of projections on the enlarged space whose compression to the ground slice
returns the original effects; the ancilla is the same for all questions, so the
identification of `ℂ^ι` with the ground slice is a single isometry serving every
question at once.  Folding the deficiency `1 - ∑_a P_a` into one distinguished
answer turns the dilated family into a complete projective measurement without
disturbing the compression, because the original effects already sum to the
identity.

Since the dilated state is the image of the original state under the two ground
embeddings, every Born probability, and hence the game value and all the
rejection, malformed-answer, cell-consistency and parity masses of the
value-to-parity layer, is unchanged.  Conversely, the local isometries produced
by a rigidity argument applied to the dilated strategy compose with the ground
embeddings to give local isometries of the original strategy, and the
state-dependent norms occurring in the conclusion of `thm:ms-rigidity` transfer
along that composition.

## References

The rigidity statement supported here is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, Theorem 6.9.  The dilation reuses the
one-measurement Naimark lemma of
`references/ldt-paper/orthonormalization.tex:121-159`, formalized as
`MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective



/-! ## Orthogonality inside a subnormalized family of projections -/

theorem solution {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] {P : α → _root_.LIDT.MIPStarRE.Quantum.Op d} (hP : ∀ a, _root_.LIDT.MIPStarRE.Quantum.IsProj (P a))
    (hsum : ∑ a, P a ≤ 1) :
    _root_.LIDT.MIPStarRE.Quantum.IsProj (∑ a, P a) := by
  classical
  constructor
  · change (∑ a, P a) * (∑ a, P a) = ∑ a, P a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_sum, Finset.sum_eq_single a]
    · exact (hP a).isIdempotentElem
    · exact fun b _ hba => _root_.MIPStarRE.QPBT.MagicSquareRigidity.mul_eq_zero_of_isProj_family hP hsum (Ne.symm hba)
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · change star (∑ a, P a) = ∑ a, P a
    rw [star_sum]
    exact Finset.sum_congr rfl fun a _ => (hP a).isSelfAdjoint
