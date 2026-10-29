-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.switchSandwich_rightTransfer
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:25.65967+00:00
-- url     : https://prove2.me/submissions/a52fe2fa-a462-4a3c-8dca-04cf85e2565e

-- Generated proof for MIPStarRE.LDT.Preliminaries.switchSandwich_rightTransfer.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
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
# Switch-sandwich main: middle-to-right transfer

The middle-to-right transfer estimate used in `prop:switch-sandwich`.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem solution
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas Question Outcome ι)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op ι) (hB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 B)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas A)
      (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas A) δ →
    |_root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B -
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.rightSandwichExpectation ψ 𝒟 A B| ≤
      Real.sqrt δ := by
  intro happrox
  have hδ :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) ≤ δ := by
    simpa [_root_.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSDDRel, _root_.LIDT.MIPStarRE.LDT.sddError, _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft,
      _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftRight] using
      happrox.leftRightSquaredDistanceBound
  have hpointwise :
      ∀ q,
        |(∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * (A q).outcome a))| ≤
          Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) := by
    intro q
    classical
    let LB : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B
    let LT : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).total)
    let RT : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) := _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).total)
    have hLB : _root_.LIDT.MIPStarRE.LDT.Preliminaries.OpBounded01 LB := by
      dsimp [LB]
      exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.leftTensor_opBounded01 (ι₂ := ι) hB
    have hLB_nonneg : 0 ≤ LB := by
      exact hLB.nonnegative
    have hLB_herm : LBᴴ = LB := by
      exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.opBounded01_hermitian hLB
    have hLB_sq_le_one : LB * LB ≤ 1 := by
      exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.opBounded01_sq_le_one hLB
    have hLT_nonneg : 0 ≤ LT := by
      dsimp [LT]
      exact _root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι) (_root_.LIDT.MIPStarRE.LDT.SubMeas.total_nonneg (A q).toSubMeas)
    have hRT_nonneg : 0 ≤ RT := by
      dsimp [RT]
      exact _root_.LIDT.MIPStarRE.LDT.rightTensor_nonneg (ι₁ := ι) (_root_.LIDT.MIPStarRE.LDT.SubMeas.total_nonneg (A q).toSubMeas)
    have hLT_herm : LTᴴ = LT := by
      exact (Matrix.nonneg_iff_posSemidef.mp hLT_nonneg).isHermitian.eq
    have hRT_herm : RTᴴ = RT := by
      exact (Matrix.nonneg_iff_posSemidef.mp hRT_nonneg).isHermitian.eq
    have hLT_proj : LT * LT = LT := by
      calc
        LT * LT
          = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((A q).total) * ((A q).total)) := by
              dsimp [LT]
              simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor] using
                (Matrix.mul_kronecker_mul
                  ((A q).total) ((A q).total)
                  (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)).symm
        _ = LT := by
              rw [_root_.LIDT.MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (A q)]
    have hRT_proj : RT * RT = RT := by
      calc
        RT * RT
          = _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (((A q).total) * ((A q).total)) := by
              dsimp [RT]
              simpa [_root_.LIDT.MIPStarRE.LDT.rightTensor] using
                (Matrix.mul_kronecker_mul
                  (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
                  ((A q).total) ((A q).total)).symm
        _ = RT := by
              rw [_root_.LIDT.MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (A q)]
    have hLTRT_comm : LT * RT = RT * LT := by
      calc
        LT * RT
          = _root_.LIDT.MIPStarRE.LDT.opTensor ((A q).total) ((A q).total) := by
              dsimp [LT, RT]
              rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
        _ = RT * LT := by
              dsimp [RT, LT]
              simpa [_root_.LIDT.MIPStarRE.LDT.rightTensor, _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                (Matrix.mul_kronecker_mul
                  (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ((A q).total)
                  ((A q).total) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
    have hLB_diag_le_one : _root_.LIDT.MIPStarRE.LDT.ev ψ (LBᴴ * LB) ≤ 1 := by
      have hmono : _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * LB) ≤ _root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) := by
        exact _root_.LIDT.MIPStarRE.LDT.ev_mono ψ _ _ hLB_sq_le_one
      simpa [hLB_herm, _root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized ψ hψ] using hmono
    have hsqrt_LB : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.ev ψ (LBᴴ * LB)) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hLB_diag_le_one
    have hLT_ev :
        _root_.LIDT.MIPStarRE.LDT.ev ψ LT =
          ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a)) := by
      dsimp [LT]
      rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψ (fun a : Outcome => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a))]
      simp [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum, (A q).sum_eq_total]
    have hRT_ev :
        _root_.LIDT.MIPStarRE.LDT.ev ψ RT =
          ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)) := by
      dsimp [RT]
      rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψ (fun a : Outcome => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))]
      simp [_root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum, (A q).sum_eq_total]
    have hdiag_le_cross :
        ∑ a,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)) ≤
          _root_.LIDT.MIPStarRE.LDT.ev ψ (LT * RT) := by
      calc
        ∑ a,
            _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))
          ≤
            ∑ a,
              ∑ b,
                _root_.LIDT.MIPStarRE.LDT.ev ψ
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome b)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              exact Finset.single_le_sum
                (fun b _ =>
                  _root_.LIDT.MIPStarRE.LDT.Preliminaries.ev_leftTensor_mul_rightTensor_nonneg ψ
                    ((A q).outcome_pos a) ((A q).outcome_pos b))
                (by simp)
        _ =
            _root_.LIDT.MIPStarRE.LDT.ev ψ (LT * RT) := by
              calc
                ∑ a,
                    ∑ b,
                      _root_.LIDT.MIPStarRE.LDT.ev ψ
                        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome b))
                  =
                    ∑ a,
                      _root_.LIDT.MIPStarRE.LDT.ev ψ
                        (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                          ∑ b,
                            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψ
                        (fun b : Outcome =>
                          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome b))]
                      rw [Matrix.mul_sum]
                _ =
                    _root_.LIDT.MIPStarRE.LDT.ev ψ
                      (∑ a,
                        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                          ∑ b,
                            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψ
                        (fun a : Outcome =>
                          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                            ∑ b,
                              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome b))]
                _ =
                    _root_.LIDT.MIPStarRE.LDT.ev ψ
                      ((∑ a,
                          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a)) *
                        ∑ b,
                          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      rw [Finset.sum_mul]
                _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (LT * RT) := by
                      simp [LT, RT, _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum, _root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum,
                        (A q).sum_eq_total]
    have htotal_sq_le :
        _root_.LIDT.MIPStarRE.LDT.ev ψ ((RT - LT)ᴴ * (RT - LT)) ≤
          _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) := by
      have hDherm : (RT - LT)ᴴ = RT - LT := by
        simp [hRT_herm, hLT_herm]
      have hD_expand :
          (RT - LT)ᴴ * (RT - LT) = RT + LT - (2 : _root_.LIDT.MIPStarRE.LDT.Error) • (LT * RT) := by
        have hmul :
            (RT - LT) * (RT - LT) = RT * RT - RT * LT - LT * RT + LT * LT := by
          noncomm_ring
        calc
          (RT - LT)ᴴ * (RT - LT)
            = (RT - LT) * (RT - LT) := by simp [hDherm]
          _ = RT * RT - RT * LT - LT * RT + LT * LT := hmul
          _ = RT + LT - (2 : _root_.LIDT.MIPStarRE.LDT.Error) • (LT * RT) := by
                rw [hRT_proj, hLT_proj, hLTRT_comm]
                simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hq_expand :
          _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) =
            (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) +
              (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a))) -
              2 *
                (∑ a,
                  _root_.LIDT.MIPStarRE.LDT.ev ψ
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) := by
        unfold _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
        calc
          ∑ a,
              _root_.LIDT.MIPStarRE.LDT.ev ψ
                ((((_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) -
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))ᴴ) *
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) -
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))))
            =
              ∑ a,
                (_root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)) +
                  _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a)) -
                  2 *
                    _root_.LIDT.MIPStarRE.LDT.ev ψ
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) := by
                refine Finset.sum_congr rfl ?_
                intro a _
                let LA : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
                  _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a)
                let RA : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
                  _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)
                have hLA_nonneg : 0 ≤ LA := by
                  dsimp [LA]
                  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_nonneg (ι₂ := ι) ((A q).outcome_pos a)
                have hRA_nonneg : 0 ≤ RA := by
                  dsimp [RA]
                  exact _root_.LIDT.MIPStarRE.LDT.rightTensor_nonneg (ι₁ := ι) ((A q).outcome_pos a)
                have hLA_herm : LAᴴ = LA := by
                  exact (Matrix.nonneg_iff_posSemidef.mp hLA_nonneg).isHermitian.eq
                have hRA_herm : RAᴴ = RA := by
                  exact (Matrix.nonneg_iff_posSemidef.mp hRA_nonneg).isHermitian.eq
                have hLA_proj : LA * LA = LA := by
                  calc
                    LA * LA
                      = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (((A q).outcome a) * ((A q).outcome a)) := by
                          dsimp [LA]
                          simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor] using
                            (Matrix.mul_kronecker_mul
                              ((A q).outcome a) ((A q).outcome a)
                              (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)).symm
                    _ = LA := by
                          rw [(A q).proj a]
                have hRA_proj : RA * RA = RA := by
                  calc
                    RA * RA
                      = _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (((A q).outcome a) * ((A q).outcome a)) := by
                          dsimp [RA]
                          simpa [_root_.LIDT.MIPStarRE.LDT.rightTensor] using
                            (Matrix.mul_kronecker_mul
                              (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
                              ((A q).outcome a) ((A q).outcome a)).symm
                    _ = RA := by
                          rw [(A q).proj a]
                have hcomm : LA * RA = RA * LA := by
                  calc
                    LA * RA
                      = _root_.LIDT.MIPStarRE.LDT.opTensor ((A q).outcome a) ((A q).outcome a) := by
                          dsimp [LA, RA]
                          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor]
                    _ = RA * LA := by
                          dsimp [RA, LA]
                          simpa [_root_.LIDT.MIPStarRE.LDT.rightTensor, _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
                            (Matrix.mul_kronecker_mul
                              (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ((A q).outcome a)
                              ((A q).outcome a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
                have hmul :
                    (LA - RA) * (LA - RA) = LA * LA - LA * RA - RA * LA + RA * RA := by
                  noncomm_ring
                calc
                  _root_.LIDT.MIPStarRE.LDT.ev ψ (((LA - RA)ᴴ) * (LA - RA))
                    = _root_.LIDT.MIPStarRE.LDT.ev ψ (RA + LA - (2 : _root_.LIDT.MIPStarRE.LDT.Error) • (LA * RA)) := by
                        rw [show (LA - RA)ᴴ = LA - RA by simp [hLA_herm, hRA_herm]]
                        rw [hmul, hLA_proj, hRA_proj, hcomm]
                        simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                  _ = _root_.LIDT.MIPStarRE.LDT.ev ψ RA + _root_.LIDT.MIPStarRE.LDT.ev ψ LA - 2 * _root_.LIDT.MIPStarRE.LDT.ev ψ (LA * RA) := by
                        rw [_root_.LIDT.MIPStarRE.LDT.ev_sub]
                        rw [_root_.LIDT.MIPStarRE.LDT.ev_add]
                        have hscale : _root_.LIDT.MIPStarRE.LDT.ev ψ ((2 : _root_.LIDT.MIPStarRE.LDT.Error) • (LA * RA)) = 2 * _root_.LIDT.MIPStarRE.LDT.ev ψ (LA * RA) := by
                          exact _root_.LIDT.MIPStarRE.LDT.ev_scale ψ (2 : _root_.LIDT.MIPStarRE.LDT.Error) (LA * RA)
                        rw [hscale]
          _ =
              (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) +
                (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a))) -
                2 *
                  (∑ a,
                    _root_.LIDT.MIPStarRE.LDT.ev ψ
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      calc
        _root_.LIDT.MIPStarRE.LDT.ev ψ ((RT - LT)ᴴ * (RT - LT))
          = _root_.LIDT.MIPStarRE.LDT.ev ψ (RT + LT - (2 : _root_.LIDT.MIPStarRE.LDT.Error) • (LT * RT)) := by
              rw [hD_expand]
        _ = _root_.LIDT.MIPStarRE.LDT.ev ψ RT + _root_.LIDT.MIPStarRE.LDT.ev ψ LT - 2 * _root_.LIDT.MIPStarRE.LDT.ev ψ (LT * RT) := by
              rw [_root_.LIDT.MIPStarRE.LDT.ev_sub, _root_.LIDT.MIPStarRE.LDT.ev_add]
              have hscale : _root_.LIDT.MIPStarRE.LDT.ev ψ ((2 : _root_.LIDT.MIPStarRE.LDT.Error) • (LT * RT)) = 2 * _root_.LIDT.MIPStarRE.LDT.ev ψ (LT * RT) := by
                exact _root_.LIDT.MIPStarRE.LDT.ev_scale ψ (2 : _root_.LIDT.MIPStarRE.LDT.Error) (LT * RT)
              rw [hscale]
        _ ≤
            (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) +
              (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a))) -
              2 *
                (∑ a,
                  _root_.LIDT.MIPStarRE.LDT.ev ψ
                    (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a) *
                      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) := by
              rw [hRT_ev, hLT_ev]
              linarith
        _ = _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) := by
              rw [hq_expand]
    have hrewrite :
        (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * (A q).outcome a)) =
          _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * (RT - LT)) := by
      have hmiddle :
          ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)) =
            _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * RT) := by
        rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψ
          (fun a : Outcome =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))]
        calc
          _root_.LIDT.MIPStarRE.LDT.ev ψ (∑ a,
              _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))
            = _root_.LIDT.MIPStarRE.LDT.ev ψ
                (LB *
                  ∑ a, _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a)) := by
                    refine congrArg (_root_.LIDT.MIPStarRE.LDT.ev ψ) ?_
                    dsimp [LB]
                    symm
                    exact Finset.mul_sum Finset.univ
                      (fun a : Outcome =>
                        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))
                      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B)
          _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * RT) := by
                simp [RT, _root_.LIDT.MIPStarRE.LDT.rightTensor_finset_sum, (A q).sum_eq_total]
      have hright :
          ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * (A q).outcome a)) =
            _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * LT) := by
        rw [← _root_.LIDT.MIPStarRE.LDT.ev_sum ψ
          (fun a : Outcome =>
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * (A q).outcome a))]
        calc
          _root_.LIDT.MIPStarRE.LDT.ev ψ (∑ a, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * (A q).outcome a))
            = _root_.LIDT.MIPStarRE.LDT.ev ψ (∑ a, LB * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a)) := by
                refine congrArg (_root_.LIDT.MIPStarRE.LDT.ev ψ) ?_
                refine Finset.sum_congr rfl ?_
                intro a _
                dsimp [LB]
                simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor] using
                  (Matrix.mul_kronecker_mul
                    B ((A q).outcome a)
                    (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
          _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * ∑ a, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((A q).outcome a)) := by
                rw [Finset.mul_sum]
          _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * LT) := by
                simp [LT, _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum, (A q).sum_eq_total]
      calc
        (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * (A q).outcome a))
          = _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * RT) - _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * LT) := by rw [hmiddle, hright]
        _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (LB * (RT - LT)) := by
              rw [(_root_.LIDT.MIPStarRE.LDT.ev_sub ψ (LB * RT) (LB * LT)).symm]
              simp [mul_sub]
    have hsqrt_LB' : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.ev ψ (LB * LBᴴ)) ≤ 1 := by
      simpa [hLB_herm] using hsqrt_LB
    calc
      |(∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) -
        ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
          (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * (A q).outcome a))|
        = |_root_.LIDT.MIPStarRE.LDT.ev ψ (LB * (RT - LT))| := by rw [hrewrite]
      _ ≤
          Real.sqrt (_root_.LIDT.MIPStarRE.LDT.ev ψ (LB * LBᴴ)) *
            Real.sqrt (_root_.LIDT.MIPStarRE.LDT.ev ψ ((RT - LT)ᴴ * (RT - LT))) := by
              simpa using _root_.LIDT.MIPStarRE.LDT.ev_abs_mul_le_sqrt ψ LB (RT - LT)
      _ ≤ 1 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.ev ψ ((RT - LT)ᴴ * (RT - LT))) := by
            exact mul_le_mul_of_nonneg_right hsqrt_LB' (Real.sqrt_nonneg _)
      _ = Real.sqrt (_root_.LIDT.MIPStarRE.LDT.ev ψ ((RT - LT)ᴴ * (RT - LT))) := by ring
      _ ≤
          Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) := by
            exact Real.sqrt_le_sqrt htotal_sq_le
  calc
    |_root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψ 𝒟 A B -
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.rightSandwichExpectation ψ 𝒟 A B|
      = |_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q =>
          (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * (A q).outcome a)))| := by
            simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.middleSandwichExpectation, _root_.LIDT.MIPStarRE.LDT.Preliminaries.rightSandwichExpectation, _root_.LIDT.MIPStarRE.LDT.avgOver,
              Finset.sum_sub_distrib, mul_sub]
    _ ≤
        Real.sqrt
          (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
            (fun q =>
              _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
          exact
            _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise 𝒟
              (fun q =>
                (∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) B *
                    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((A q).outcome a))) -
                ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
                  (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B * (A q).outcome a)))
              (fun q =>
                _root_.LIDT.MIPStarRE.LDT.qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
              hpointwise
              (fun q => _root_.LIDT.MIPStarRE.LDT.qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
              h𝒟
    _ ≤ Real.sqrt δ := by
          exact Real.sqrt_le_sqrt hδ
