-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.norm_rightTensor_one_sub_groundProjection_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:27:31.083512+00:00
-- url     : https://prove2.me/submissions/c383589c-e337-4697-a82f-47f08be7659a

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.norm_rightTensor_one_sub_groundProjection_mul_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_applyOperatorToState_rightTensor_one_sub_groundProjection

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/



/-- Operators act additively on states. -/
theorem applyOperatorToState_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (u v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState M (u + v) =
      _root_.MIPStarRE.QPBT.applyOperatorToState M u + _root_.MIPStarRE.QPBT.applyOperatorToState M v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]





/-- Operators annihilate the zero state. -/
theorem applyOperatorToState_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState M (0 : EuclideanSpace ℂ ι) = 0 := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]









/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h



/-- Orthogonal projections are contractions. -/
theorem conjTranspose_mul_le_one_of_isProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hP : _root_.LIDT.MIPStarRE.Quantum.IsProj P) : Pᴴ * P ≤ 1 := by
  have hstar : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  rw [hstar, hP.isIdempotentElem.eq]
  exact sub_nonneg.mp hP.one_sub.nonneg









/-- Right placement preserves contractions. -/
theorem conjTranspose_mul_le_one_rightTensor {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {B : _root_.LIDT.MIPStarRE.Quantum.Op ιB} (hB : Bᴴ * B ≤ 1) :
    (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B)ᴴ * _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B ≤ 1 := by
  change (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) B)ᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) B ≤ 1
  rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_conjTranspose, _root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor]
  exact _root_.LIDT.MIPStarRE.LDT.rightTensor_le_one hB

/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/



/-- Inflation is multiplicative. -/
theorem naimarkInflation_mul {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M * _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) N =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) (M * N) := by
  ext p q
  simp only [Matrix.mul_apply, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_apply, Fintype.sum_prod_type,
    Fintype.sum_option]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- Inflation commutes with the conjugate transpose. -/
theorem naimarkInflation_conjTranspose {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M)ᴴ = _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) Mᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_apply]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- The ground projection is an orthogonal projection. -/
theorem isProj_groundProjection (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α) := by
  constructor
  · change _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α = _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_mul, Matrix.mul_one]
  · change star (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α
    rw [Matrix.star_eq_conjTranspose, _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_conjTranspose,
      Matrix.conjTranspose_one]













/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Contractions and their action on states -/



































/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/

theorem solution (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))
    (P : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × Option α)) (Q : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α)) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α) * Q))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron P 1 - _root_.MIPStarRE.QPBT.heteroKron 1 Q)
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ := by
  set ψ' := _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ
  set L : _root_.LIDT.MIPStarRE.Quantum.Op ((ιA × Option α) × (ιB × Option α)) :=
    _root_.MIPStarRE.QPBT.heteroKron 1 (1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α)
  have hL0 : _root_.MIPStarRE.QPBT.applyOperatorToState L ψ' = 0 :=
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_rightTensor_one_sub_groundProjection α ψ
  have hLcontr : Lᴴ * L ≤ 1 :=
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isProj_groundProjection ιB α).one_sub)
  have hsplit : _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × Option α))
      ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α) * Q) = L * _root_.MIPStarRE.QPBT.heteroKron 1 Q := by
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.one_mul]
  have hcomm : L * _root_.MIPStarRE.QPBT.heteroKron P 1 = _root_.MIPStarRE.QPBT.heteroKron P 1 * L := by
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one]
  have key : _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α) * Q)) ψ' =
      _root_.MIPStarRE.QPBT.applyOperatorToState L
        (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 Q - _root_.MIPStarRE.QPBT.heteroKron P 1) ψ') := by
    rw [hsplit, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
    have hdec : _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 Q) ψ' =
        _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 Q - _root_.MIPStarRE.QPBT.heteroKron P 1) ψ' +
          _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron P 1) ψ' := by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    rw [hdec, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_add, ← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul L (_root_.MIPStarRE.QPBT.heteroKron P 1), hcomm,
      _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, hL0, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_zero, add_zero]
  have hneg : -_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron P 1 - _root_.MIPStarRE.QPBT.heteroKron 1 Q) ψ' =
      _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 Q - _root_.MIPStarRE.QPBT.heteroKron P 1) ψ' := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  rw [key]
  calc ‖_root_.MIPStarRE.QPBT.applyOperatorToState L
          (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 Q - _root_.MIPStarRE.QPBT.heteroKron P 1) ψ')‖ ≤
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 Q - _root_.MIPStarRE.QPBT.heteroKron P 1) ψ'‖ :=
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le hLcontr _
    _ = ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron P 1 - _root_.MIPStarRE.QPBT.heteroKron 1 Q) ψ'‖ := by
        rw [← hneg, norm_neg]
