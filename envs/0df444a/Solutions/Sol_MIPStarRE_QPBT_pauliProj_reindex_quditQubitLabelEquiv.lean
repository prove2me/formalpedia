-- Prove2me | solution 1 for MIPStarRE.QPBT.pauliProj_reindex_quditQubitLabelEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:57:53.790495+00:00
-- url     : https://prove2.me/submissions/a660d453-c787-4553-a904-16535da9174e

-- Generated proof for MIPStarRE.QPBT.pauliProj_reindex_quditQubitLabelEquiv.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Algebra_PauliTheorems
import Definitions.Def_QPBT_QPBT_Algebra_SelfDualBasis
import Definitions.Def_QPBT_QPBT_Algebra_SelfDualBasisTheorems
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_pauliProj_eq_avg_tauObservable
import Theorems.Thm_MIPStarRE_QPBT_trace_mul_eq_dotProduct_basisCoord

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Algebra/SelfDualBasisTheorems.lean. -/
/-! # Trace and coordinate identities for self-dual bases

Blueprint `lem:downsize_field` and `lem:one`; paper
`references/qpbt-paper/04_preliminaries.tex:505-550,730-767`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

-- The paper-facing interface fixes `Fintype ι`; its value is needed only for the matrix sum.






-- The finite carrier is part of the fixed source-aligned interface for the binary field model.


-- The finite carrier is part of the fixed source-aligned interface for the binary field model.










/-- Canonical specialization of item 2 of blueprint
`lem:downsize_field`, paper `04_preliminaries.tex:509-550`. -/
theorem binTrace_mul_eq_dotProduct {q : ℕ} (F : _root_.MIPStarRE.QPBT.FixedFieldModel q)
    (x y : F.K) :
    _root_.MIPStarRE.QPBT.binTrace F.K (x * y) = dotProduct (F.binaryCoordinates x) (F.binaryCoordinates y) := by
  apply _root_.MIPStarRE.QPBT.trace_mul_eq_dotProduct_basisCoord F.basis
  simpa [_root_.MIPStarRE.QPBT.Basis.IsSelfDual, _root_.MIPStarRE.QPBT.IsDualBasisPair] using F.selfDual



-- The fixed interface supplies decidable basis indices for the multiplication-table calculation.






end MIPStarRE.QPBT

/- Source helpers from QPBT/Algebra/PauliTheorems.lean. -/
/-! # Pauli product, commutation, and cancellation identities

The principal results are blueprint `lem:twisted-commutation` and
`lem:cancellation`, from
`references/qpbt-paper/04_preliminaries.tex:1056-1095,1124-1151`. The
general-prime statements use the canonical character `ffChar`; binary
declarations below are separately named QPBT specializations.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum



































































/-- The label equivalence is the uncurried form of `kappaVec`. -/
private theorem quditQubitLabelEquiv_eq_kappaVec {q : ℕ} {ι : Type*}
    (F : _root_.MIPStarRE.QPBT.FixedFieldModel q) (u : ι → F.K) :
    _root_.MIPStarRE.QPBT.quditQubitLabelEquiv F u = _root_.MIPStarRE.QPBT.kappaVec F u := by
  rfl

/-- Self-duality identifies the field trace pairing with the binary coordinate
pairing after relabeling. -/
private theorem binTrace_dotProduct_eq_quditQubitLabelEquiv
    {q : ℕ} {ι : Type*} [Fintype ι] (F : _root_.MIPStarRE.QPBT.FixedFieldModel q) (a u : ι → F.K) :
    _root_.MIPStarRE.QPBT.binTrace F.K (dotProduct a u) =
      _root_.MIPStarRE.QPBT.binTrace (ZMod 2)
        (dotProduct (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F a) (_root_.MIPStarRE.QPBT.kappaVec F u)) := by
  simp only [dotProduct, map_sum, _root_.MIPStarRE.QPBT.binTrace_mul_eq_dotProduct F,
    Algebra.trace_self_apply, Fintype.sum_prod_type, _root_.MIPStarRE.QPBT.quditQubitLabelEquiv,
    Equiv.trans_apply, Equiv.curry_symm_apply, _root_.MIPStarRE.QPBT.kappaVec, _root_.MIPStarRE.QPBT.basisCoordVec]
  rfl

/-- The coordinate label equivalence preserves addition. -/
private theorem quditQubitLabelEquiv_add {q : ℕ} {ι : Type*}
    (F : _root_.MIPStarRE.QPBT.FixedFieldModel q) (a b : ι → F.K) :
    _root_.MIPStarRE.QPBT.quditQubitLabelEquiv F (a + b) =
      _root_.MIPStarRE.QPBT.quditQubitLabelEquiv F a + _root_.MIPStarRE.QPBT.quditQubitLabelEquiv F b := by
  ext p
  rcases p with ⟨i, j⟩
  change F.binaryCoordinates (a i + b i) j =
    F.binaryCoordinates (a i) j + F.binaryCoordinates (b i) j
  simp

/-- A shift observable is the permutation matrix for addition by its label. -/
theorem tauObservable_X_apply
    {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (a x y : ι → K) :
    _root_.MIPStarRE.QPBT.tauObservable .X a x y = if x = y + a then 1 else 0 := by
  change (∏ i : ι, if x i = y i + a i then 1 else 0) = _
  rw [Fintype.prod_boole]
  have hsupport : (∀ i, x i = y i + a i) ↔ x = y + a := by
    simpa only [Pi.add_apply] using
      (funext_iff (f := x) (g := y + a)).symm
  simp only [hsupport]

/-- A phase observable is diagonal, with its phase given by the trace pairing. -/
theorem tauObservable_Z_apply
    {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (a x y : ι → K) :
    _root_.MIPStarRE.QPBT.tauObservable .Z a x y =
      if x = y then _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct a y)) else 0 := by
  change
    (∏ i : ι,
      if x i = y i then _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (a i * y i)) else 0) = _
  rw [Fintype.prod_ite_zero, _root_.MIPStarRE.QPBT.prod_phaseSign_binTrace_dotProduct]
  have hsupport : (∀ i, x i = y i) ↔ x = y :=
    (funext_iff (f := x) (g := y)).symm
  simp only [hsupport]

/-- Binary-coordinate relabeling transports both generalized Pauli observables. -/
private theorem tauObservable_reindex_quditQubitLabelEquiv
    {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (F : _root_.MIPStarRE.QPBT.FixedFieldModel q)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (a : ι → F.K) :
    _root_.MIPStarRE.QPBT.tauObservable W a =
      Matrix.reindex (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F).symm
        (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F).symm
        (_root_.MIPStarRE.QPBT.tauObservable W (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F a)) := by
  classical
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  cases W with
  | X =>
      rw [_root_.MIPStarRE.QPBT.tauObservable_X_apply, _root_.MIPStarRE.QPBT.tauObservable_X_apply]
      have hadd := quditQubitLabelEquiv_add F y a
      rw [← hadd]
      by_cases hshift : x = y + a
      · rw [if_pos hshift, if_pos]
        exact congrArg (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F) hshift
      · rw [if_neg hshift, if_neg]
        exact fun h => hshift ((_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F).injective h)
  | Z =>
      rw [_root_.MIPStarRE.QPBT.tauObservable_Z_apply, _root_.MIPStarRE.QPBT.tauObservable_Z_apply]
      by_cases hxy : x = y
      · subst y
        rw [if_pos rfl, if_pos rfl,
          binTrace_dotProduct_eq_quditQubitLabelEquiv,
          quditQubitLabelEquiv_eq_kappaVec F a,
          quditQubitLabelEquiv_eq_kappaVec F x]
      · have hlabels : _root_.MIPStarRE.QPBT.quditQubitLabelEquiv F x ≠
            _root_.MIPStarRE.QPBT.quditQubitLabelEquiv F y := fun h =>
          hxy ((_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F).injective h)
        rw [if_neg hxy, if_neg hlabels]







end MIPStarRE.QPBT

/-! # Pauli product, commutation, and cancellation identities

The principal results are blueprint `lem:twisted-commutation` and
`lem:cancellation`, from
`references/qpbt-paper/04_preliminaries.tex:1056-1095,1124-1151`. The
general-prime statements use the canonical character `ffChar`; binary
declarations below are separately named QPBT specializations.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum

theorem solution
    {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (F : _root_.MIPStarRE.QPBT.FixedFieldModel q)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (u : ι → F.K) :
    _root_.MIPStarRE.QPBT.pauliProj W u =
      Matrix.reindex (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F).symm
        (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F).symm
        (_root_.MIPStarRE.QPBT.pauliProj W (_root_.MIPStarRE.QPBT.kappaVec F u)) := by
  classical
  rw [_root_.MIPStarRE.QPBT.pauliProj_eq_avg_tauObservable, _root_.MIPStarRE.QPBT.pauliProj_eq_avg_tauObservable]
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [Fintype.card_congr (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv (ι := ι) F)]
  congr 1
  apply Fintype.sum_equiv (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F)
  intro a
  have hphase := congrArg _root_.MIPStarRE.QPBT.phaseSign
    (binTrace_dotProduct_eq_quditQubitLabelEquiv F a u)
  have hentry := congrFun
    (congrFun (tauObservable_reindex_quditQubitLabelEquiv F W a) x) y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] at hentry
  rw [hphase, hentry]
