-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_naimarkDilatedEffect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:08:26.303557+00:00
-- url     : https://prove2.me/submissions/6ca012bc-1f66-4d8e-b602-33f9128bcf70

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_naimarkDilatedEffect.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_OneMeasNaimarkData_compression_none_none
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_oneMeasNaimark

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







/-! ## The ground slice of an enlarged local space -/













/-- The compression to the ground slice is additive. -/
theorem naimarkCompression_add {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × Option α)) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) (M + N) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) M + _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) N := by
  ext i j; simp

/-- The compression to the ground slice commutes with finite sums. -/
theorem naimarkCompression_sum {ι α β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Fintype β] (M : β → _root_.LIDT.MIPStarRE.Quantum.Op (ι × Option α)) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) (∑ b, M b) = ∑ b, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) (M b) := by
  ext i j; simp [Matrix.sum_apply]









/-- The compression to the ground slice respects differences. -/
theorem naimarkCompression_sub {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × Option α)) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) (M - N) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) M - _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) N := by
  ext i j; simp

/-! ## The dilated projective measurement -/



/-- The chosen dilation dilates the intended measurement. -/
theorem naimarkData_source {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d) :
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkData M).source = M.toSubmeasurement :=
  Classical.choose_spec (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark M.toSubmeasurement)





















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







/-! ## The ground slice of an enlarged local space -/



























/-! ## The dilated projective measurement -/

theorem solution {α d : Type} [Fintype α] [DecidableEq α]
    [Fintype d] [DecidableEq d] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d) (a₀ a : α) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedEffect M a₀ a) = M.effect a := by
  have hlift : ∀ b : α,
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkData M).liftedEffect (some b)) = M.effect b := by
    intro b
    ext i j
    have h := (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkData M).compression_none_none b i j
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkData_source M] at h
    simpa using h
  have hdef : _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression
      (1 - ∑ b : α, (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkData M).liftedEffect (some b)) = 0 := by
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_sub, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_one, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_sum]
    simp only [hlift]
    rw [M.sum_eq_one, sub_self]
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedEffect
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_add, hlift]
  by_cases h : a = a₀
  · simp [h, hdef]
  · simp [h]
