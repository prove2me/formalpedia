-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.question_switchSandwich_middle_gap
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:26:51.609261+00:00
-- url     : https://prove2.me/submissions/f29435fe-a9c6-43e1-8226-868ac1ade063

-- Generated proof for MIPStarRE.LDT.Preliminaries.question_switchSandwich_middle_gap.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_sum_ev_mul_leftBounded_le_of_leftHermitian

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/Core.lean. -/
/-! ### Bridge lemmas for `prop:switch-sandwich` -/

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

@[expose] public section















/-- Any `OpBounded01` operator is Hermitian. -/
lemma opBounded01_hermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    Bᴴ = B :=
  (Matrix.nonneg_iff_posSemidef.mp hB.nonnegative).isHermitian.eq

/-- Any `OpBounded01` operator satisfies `B * B ≤ 1`. -/
lemma opBounded01_sq_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    B * B ≤ 1 := by
  have hB_le_one : B ≤ 1 := sub_nonneg.mp hB.boundedByIdentity
  exact le_trans
    (MIPStarRE.Quantum.sq_le_self hB.nonnegative hB_le_one)
    hB_le_one

/-- Left tensoring preserves the `0 ≤ B ≤ 1` bounds. -/
lemma leftTensor_opBounded01
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {B : MIPStarRE.Quantum.Op ι₁} (hB : OpBounded01 B) :
    OpBounded01 (leftTensor (ι₂ := ι₂) B) := by
  constructor
  · exact leftTensor_nonneg (ι₂ := ι₂) hB.nonnegative
  · exact sub_nonneg.mpr
      (leftTensor_le_one (ι₂ := ι₂) (sub_nonneg.mp hB.boundedByIdentity))

end

end MIPStarRE.LDT.Preliminaries

end LIDT

open LIDT
/-!
# Switch-sandwich gap bounds: middle gap

The middle gap estimate `question_switchSandwich_middle_gap`, bounding the
question-level middle gap of the switch-sandwich argument.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem solution
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas Outcome ι)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op ι) (hB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 B) :
    |(∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))| ≤
      Real.sqrt
        (_root_.LIDT.MIPStarRE.LDT.qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
  let LB : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B
  have hLB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 LB := by
    dsimp [LB]
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.leftTensor_opBounded01 (ι₂ := ι) hB
  have hLB_nonneg : 0 ≤ LB := by
    exact hLB.nonnegative
  have hLB_herm : LBᴴ = LB := by
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.opBounded01_hermitian hLB
  have hLB_sq_le_one : LB * LB ≤ 1 := by
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.opBounded01_sq_le_one hLB
  have hLAherm :
      ∀ a : Outcome,
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a))ᴴ =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι) (A.outcome_pos a))).isHermitian.eq
  have hRAherm :
      ∀ a : Outcome,
        (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.LDT.rightTensor_nonneg (ι₁ := ι) (A.outcome_pos a))).isHermitian.eq
  have hDherm :
      ∀ a : Outcome,
        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    simp [hLAherm a, hRAherm a]
  have haux :
      |∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))) *
        Real.sqrt
          (∑ a : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) := by
    simpa [hRAherm] using
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.sum_ev_mul_leftBounded_le_of_leftHermitian ψ LB
        (fun a =>
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))
        (fun a => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))
        hLB_herm hLB_sq_le_one hDherm hRAherm
  have hdiag_le_one :
      ∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) ≤ 1 := by
    simpa [_root_.LIDT.MIPStarRE.LDT.SubMeas.liftRight] using
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_one ψ hψ A.toSubMeas.liftRight
  have hsqrt_diag :
      Real.sqrt
        (∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiag_le_one
  have haux' :
      |∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))) := by
    calc
      |∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))|
        ≤
          Real.sqrt
            (∑ a : Outcome,
              _root_.LIDT.MIPStarRE.LDT.ev ψ
                ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))) *
            Real.sqrt
              (∑ a : Outcome,
                _root_.LIDT.MIPStarRE.LDT.ev ψ
                  (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) := haux
      _ ≤
          Real.sqrt
            (∑ a : Outcome,
              _root_.LIDT.MIPStarRE.LDT.ev ψ
                ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrt_diag (Real.sqrt_nonneg _)
      _ =
          Real.sqrt
            (∑ a : Outcome,
              _root_.LIDT.MIPStarRE.LDT.ev ψ
                ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))) := by
            ring
  have hrewrite :
      ∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) -
      ∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))
        =
      ∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
            (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) := by
    calc
      (∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) -
          ∑ a : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))
        =
        ∑ a : Outcome,
          (_root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) -
            _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ a : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψ
              ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
                (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [(_root_.LIDT.MIPStarRE.LDT.ev_sub ψ
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))).symm]
            have hRcomm :
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B =
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) := by
              calc
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
                    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B
                  = _root_.LIDT.MIPStarRE.LDT.opTensor B (A.outcome a) := by
                      simpa [_root_.LIDT.MIPStarRE.LDT.rightTensor, _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                        (Matrix.mul_kronecker_mul
                          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) B
                          (A.outcome a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)).symm
                _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) := by
                      rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
            refine congrArg (_root_.LIDT.MIPStarRE.LDT.ev ψ) ?_
            have hRA_mul :
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
                    (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) =
                  LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) := by
              calc
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
                    (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))
                  = (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) * LB) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) := by
                        simp [mul_assoc]
                _ = (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) := by
                        rw [hRcomm]
                _ = LB *
                      (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) := by
                        simp [mul_assoc]
                _ = LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) := by
                      have hRAproj :
                          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
                              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) =
                            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) := by
                        simpa [_root_.LIDT.MIPStarRE.LDT.rightTensor, A.proj a] using
                          (Matrix.mul_kronecker_mul
                            (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
                            (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
                            (A.outcome a) (A.outcome a)).symm
                      simp [hRAproj]
            calc
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) -
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)
                =
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
                    (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) -
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a) *
                    (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) := by
                    simp [LB, mul_assoc, hRA_mul]
              _ =
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
                  (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) := by
                    simp [sub_mul]
  calc
    |(∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))|
      = |∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))| := by
            rw [hrewrite]
    _ ≤ Real.sqrt
          (∑ a : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψ
              ((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)) *
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (A.outcome a) -
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a)))) := haux'
    _ = Real.sqrt (_root_.LIDT.MIPStarRE.LDT.qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
          simp [_root_.LIDT.MIPStarRE.LDT.qSDD, _root_.LIDT.MIPStarRE.LDT.qSDDCore, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftRight, hDherm]
