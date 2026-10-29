-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_axisParallel_eq_roleAverage
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:12:25.436218+00:00
-- url     : https://prove2.me/submissions/74f401b7-8ae3-442b-8359-b5f65917cac1

-- Generated proof for MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_axisParallel_eq_roleAverage.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_qBipartiteConsDefect_of_measurements

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.ProjStrat
end LIDT.MIPStarRE.LDT.ProjStrat

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Core.lean. -/
/-!
# Role-Register Averaging: Branch Equalities

This module proves the role-register branch equalities for heterogeneous
projective strategies.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat

theorem ev_roleRegisterSymmState_rolePairDirectSumCond_AA {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    ev (roleRegisterSymmState ψ) (rolePairDirectSumCond Role.A Role.A X) = 0 := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.A Role.A X)) = 0
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.A Role.B Role.A Role.A
      (localPairABBlock ψ.density) X (by decide)]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.B Role.A Role.A Role.A
      (localPairBABlock (heterogeneousSwapDensity ψ.density)) X (by decide)]
  simp

theorem ev_roleRegisterSymmState_rolePairDirectSumCond_BB {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    ev (roleRegisterSymmState ψ) (rolePairDirectSumCond Role.B Role.B X) = 0 := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.B Role.B X)) = 0
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.A Role.B Role.B Role.B
      (localPairABBlock ψ.density) X (by decide)]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.B Role.A Role.B Role.B
      (localPairBABlock (heterogeneousSwapDensity ψ.density)) X (by decide)]
  simp

private lemma opTensor_roleBlock_eq_rolePairDirectSumCond_sum {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A B C D : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    opTensor (roleBlock A B) (roleBlock C D) =
      rolePairDirectSumCond Role.A Role.A (opTensor A C) +
        rolePairDirectSumCond Role.A Role.B (opTensor A D) +
          (rolePairDirectSumCond Role.B Role.A (opTensor B C) +
            rolePairDirectSumCond Role.B Role.B (opTensor B D)) := by
  ext x y
  rcases x with ⟨⟨rx, ix⟩, ⟨sx, jx⟩⟩
  rcases y with ⟨⟨ry, iy⟩, ⟨sy, jy⟩⟩
  cases rx <;> cases sx <;> cases ry <;> cases sy <;>
    simp [opTensor, rolePairDirectSumCond, rolePairProj, roleProj,
      roleRegisterPairLocalEquiv]

private lemma localPairABBlock_mul_opTensor_localDirectSumBlocks {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Afill : MIPStarRE.Quantum.Op ιA) (D : MIPStarRE.Quantum.Op ιB) :
    localPairABBlock X *
        opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Afill D) =
      localPairABBlock (X * opTensor A D) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ with
      | inl j =>
          cases y₁ <;> cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]
      | inr j =>
          cases y₁ with
          | inl i' =>
              cases y₂ with
              | inl j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp [localPairABBlock, opTensor]
              | inr j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairABBlock, opTensor,
                    localDirectSumBlock, Matrix.of_apply, zero_mul, Finset.sum_const_zero,
                    zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιA => fun y : ιB =>
                      X (i, j) (x, y) * (A x i' * D y j'))).symm
          | inr i' =>
              cases y₂ <;>
                rw [Matrix.mul_apply, Fintype.sum_prod_type] <;>
                simp [localPairABBlock, opTensor]
  | inr i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;>
        simp [localPairABBlock, Matrix.mul_apply]

private lemma localPairBABlock_mul_opTensor_localDirectSumBlocks {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA))
    (B : MIPStarRE.Quantum.Op ιB) (Afill : MIPStarRE.Quantum.Op ιA)
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB) :
    localPairBABlock X *
        opTensor (localDirectSumBlock Afill B) (localDirectSumBlock A Bfill) =
      localPairBABlock (X * opTensor B A) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;>
        simp [localPairBABlock, Matrix.mul_apply]
  | inr i =>
      cases x₂ with
      | inl j =>
          cases y₁ with
          | inl i' =>
              cases y₂ <;>
                rw [Matrix.mul_apply, Fintype.sum_prod_type] <;>
                simp [localPairBABlock, opTensor]
          | inr i' =>
              cases y₂ with
              | inl j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairBABlock, opTensor,
                    localDirectSumBlock, Matrix.of_apply, zero_mul, Finset.sum_const_zero,
                    zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιB => fun y : ιA =>
                      X (i, j) (x, y) * (B x i' * A y j'))).symm
              | inr j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp [localPairBABlock, opTensor]
      | inr j =>
          cases y₁ <;> cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]

private lemma ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Afill : MIPStarRE.Quantum.Op ιA) (D : MIPStarRE.Quantum.Op ιB) :
    ev (roleRegisterSymmState ψ)
        (rolePairDirectSumCond Role.A Role.B
          (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Afill D))) =
      (1 / 2 : Error) * ev ψ (opTensor A D) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.A Role.B
          (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Afill D)))) =
    (1 / 2 : Error) * ev ψ (opTensor A D)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_same, rolePairDirectSumCond_BA_mul_AB]
  rw [localPairABBlock_mul_opTensor_localDirectSumBlocks]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, add_zero]
  rw [normalizedTrace_rolePairDirectSumCond, normalizedTrace_localPairABBlock]
  let T := MIPStarRE.Quantum.normalizedTrace (ψ.density * opTensor A D)
  let R : ℂ :=
    (Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
      ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscalar :
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R) = (1 / 2 : ℂ) := by
    subst R
    unfold roleRegisterDensityScale
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
    ring_nf
  change Complex.re ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T))) =
    (1 / 2 : Error) * ev ψ (opTensor A D)
  rw [show ev ψ (opTensor A D) = Complex.re T by rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (B : MIPStarRE.Quantum.Op ιB) (Afill : MIPStarRE.Quantum.Op ιA)
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB) :
    ev (roleRegisterSymmState ψ)
        (rolePairDirectSumCond Role.B Role.A
          (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock A Bfill))) =
      (1 / 2 : Error) * ev ψ (opTensor A B) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.B Role.A
          (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock A Bfill)))) =
    (1 / 2 : Error) * ev ψ (opTensor A B)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_AB_mul_BA, rolePairDirectSumCond_mul_same]
  rw [localPairBABlock_mul_opTensor_localDirectSumBlocks]
  rw [← heterogeneousSwapDensity_opTensor]
  rw [← heterogeneousSwapDensity_mul]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, zero_add]
  rw [normalizedTrace_rolePairDirectSumCond, normalizedTrace_localPairBABlock,
    normalizedTrace_heterogeneousSwapDensity]
  let T := MIPStarRE.Quantum.normalizedTrace (ψ.density * opTensor A B)
  let R : ℂ :=
    (Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
      ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscalar :
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R) = (1 / 2 : ℂ) := by
    subst R
    unfold roleRegisterDensityScale
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
    ring_nf
  change Complex.re ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T))) =
    (1 / 2 : Error) * ev ψ (opTensor A B)
  rw [show ev ψ (opTensor A B) = Complex.re T by rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma ev_roleRegisterSymmState_roleBlock_localDirectSumBlocks
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A C Afill Cfill : MIPStarRE.Quantum.Op ιA)
    (B D Bfill Dfill : MIPStarRE.Quantum.Op ιB) :
    ev (roleRegisterSymmState ψ)
        (opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          (roleBlock (localDirectSumBlock C Dfill) (localDirectSumBlock Cfill D))) =
      (1 / 2 : Error) * ev ψ (opTensor A D) +
        (1 / 2 : Error) * ev ψ (opTensor C B) := by
  calc
    ev (roleRegisterSymmState ψ)
        (opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          (roleBlock (localDirectSumBlock C Dfill) (localDirectSumBlock Cfill D)))
      = ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock C Dfill)) +
            rolePairDirectSumCond Role.A Role.B
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Cfill D)) +
              (rolePairDirectSumCond Role.B Role.A
                (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock C Dfill)) +
                rolePairDirectSumCond Role.B Role.B
                  (opTensor (localDirectSumBlock Afill B)
                    (localDirectSumBlock Cfill D)))) := by
          rw [opTensor_roleBlock_eq_rolePairDirectSumCond_sum]
    _ =
        ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock C Dfill))) +
          ev (roleRegisterSymmState ψ)
            (rolePairDirectSumCond Role.A Role.B
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Cfill D))) +
            (ev (roleRegisterSymmState ψ)
              (rolePairDirectSumCond Role.B Role.A
                (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock C Dfill))) +
              ev (roleRegisterSymmState ψ)
                (rolePairDirectSumCond Role.B Role.B
                  (opTensor (localDirectSumBlock Afill B)
                    (localDirectSumBlock Cfill D)))) := by
          repeat rw [ev_add]
    _ = 0 + (1 / 2 : Error) * ev ψ (opTensor A D) +
            ((1 / 2 : Error) * ev ψ (opTensor C B) + 0) := by
          rw [ev_roleRegisterSymmState_rolePairDirectSumCond_AA,
            ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePairDirectSumCond_BB]
    _ = (1 / 2 : Error) * ev ψ (opTensor A D) +
        (1 / 2 : Error) * ev ψ (opTensor C B) := by
          ring



private lemma postprocess_roleRegisterProjMeas_outcome
    {α β ιA ιB : Type*}
    [Inhabited α] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas α ιA) (MB : ProjMeas α ιB) (f : α → β) (b : β) :
    (postprocess ((roleRegisterProjMeas MA MB).toSubMeas) f).outcome b =
      roleBlock
        (localDirectSumBlock ((ProjMeas.postprocess MA f).outcome b)
          ((ProjMeas.postprocess
            (ProjMeas.trivialDistinguishedOutcome (ι := ιB) (default : α)) f).outcome b))
        (localDirectSumBlock
          ((ProjMeas.postprocess
            (ProjMeas.trivialDistinguishedOutcome (ι := ιA) (default : α)) f).outcome b)
          ((ProjMeas.postprocess MB f).outcome b)) := by
  classical
  rw [SubMeas.postprocess_outcome]
  simp only [roleRegisterProjMeas, roleBlockProjMeas_outcome,
    localDirectSumProjMeas_outcome, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_outcome]
  rw [roleBlock_finset_sum]
  rw [localDirectSumBlock_finset_sum, localDirectSumBlock_finset_sum]

private lemma ev_roleRegisterSymmState_point_postprocessedLine_outcome
    {α β ιA ιB : Type*}
    [Inhabited α] [Inhabited β] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (PA : ProjMeas β ιA) (PB : ProjMeas β ιB)
    (LA : ProjMeas α ιA) (LB : ProjMeas α ιB)
    (f : α → β) (b : β) :
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas PA PB).outcome b)
          ((postprocess ((roleRegisterProjMeas LA LB).toSubMeas) f).outcome b)) =
      (1 / 2 : Error) *
          ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
        (1 / 2 : Error) *
          ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b)) := by
  let fillerAβ : ProjMeas β ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerBβ : ProjMeas β ιB := ProjMeas.trivialDistinguishedOutcome default
  rw [postprocess_roleRegisterProjMeas_outcome]
  change ev (roleRegisterSymmState ψ)
      (opTensor
        (roleBlock (localDirectSumBlock (PA.outcome b) (fillerBβ.outcome b))
          (localDirectSumBlock (fillerAβ.outcome b) (PB.outcome b)))
        (roleBlock
          (localDirectSumBlock ((ProjMeas.postprocess LA f).outcome b)
            ((ProjMeas.postprocess
              (ProjMeas.trivialDistinguishedOutcome (ι := ιB) (default : α)) f).outcome b))
          (localDirectSumBlock
            ((ProjMeas.postprocess
              (ProjMeas.trivialDistinguishedOutcome (ι := ιA) (default : α)) f).outcome b)
            ((ProjMeas.postprocess LB f).outcome b)))) =
    (1 / 2 : Error) *
        ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
      (1 / 2 : Error) *
        ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b))
  exact ev_roleRegisterSymmState_roleBlock_localDirectSumBlocks ψ
    (PA.outcome b) ((ProjMeas.postprocess LA f).outcome b)
    (fillerAβ.outcome b)
    ((ProjMeas.postprocess
      (ProjMeas.trivialDistinguishedOutcome (ι := ιA) (default : α)) f).outcome b)
    (PB.outcome b) ((ProjMeas.postprocess LB f).outcome b)
    (fillerBβ.outcome b)
    ((ProjMeas.postprocess
      (ProjMeas.trivialDistinguishedOutcome (ι := ιB) (default : α)) f).outcome b)

private lemma qBipartiteMatchMass_roleRegister_point_postprocessedLine_eq_average
    {α β ιA ιB : Type*}
    [Inhabited α] [Inhabited β] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (PA : ProjMeas β ιA) (PB : ProjMeas β ιB)
    (LA : ProjMeas α ιA) (LB : ProjMeas α ιB) (f : α → β) :
    qBipartiteMatchMass (roleRegisterSymmState ψ)
        (roleRegisterProjMeas PA PB).toSubMeas
        ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) =
      (qBipartiteMatchMass ψ PA.toSubMeas (ProjMeas.postprocess LB f).toSubMeas +
        qBipartiteMatchMass ψ (ProjMeas.postprocess LA f).toSubMeas PB.toSubMeas) / 2 := by
  unfold qBipartiteMatchMass
  calc
    ∑ b : β,
        ev (roleRegisterSymmState ψ)
          (opTensor ((roleRegisterProjMeas PA PB).outcome b)
            (((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas).outcome b))
      = ∑ b : β,
          ((1 / 2 : Error) *
              ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
            (1 / 2 : Error) *
              ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b))) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            exact ev_roleRegisterSymmState_point_postprocessedLine_outcome
              ψ PA PB LA LB f b
    _ = (1 / 2 : Error) *
          ∑ b : β, ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
        (1 / 2 : Error) *
          ∑ b : β, ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ =
        (∑ b : β, ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
          ∑ b : β, ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b)
            (PB.outcome b))) / 2 := by
          ring

private lemma qBipartiteConsDefect_roleRegister_point_postprocessedLine_eq_average
    {α β ιA ιB : Type*}
    [Inhabited α] [Inhabited β] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (PA : ProjMeas β ιA) (PB : ProjMeas β ιB)
    (LA : ProjMeas α ιA) (LB : ProjMeas α ιB) (f : α → β) :
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas PA PB).toSubMeas
        ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) =
      (qBipartiteConsDefect ψ PA.toSubMeas (ProjMeas.postprocess LB f).toSubMeas +
        qBipartiteConsDefect ψ (ProjMeas.postprocess LA f).toSubMeas PB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas PA PB).toSubMeas
        ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas)
      = ev (roleRegisterSymmState ψ)
          (1 : MIPStarRE.Quantum.Op
            (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas PA PB).toSubMeas
            ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) := by
            exact qBipartiteConsDefect_of_measurements (roleRegisterSymmState ψ)
              (roleRegisterProjMeas PA PB).toMeasurement
              (ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toMeasurement
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas PA PB).toSubMeas
            ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) := by
            rw [ev_one_of_isNormalized (roleRegisterSymmState ψ)
              (roleRegisterSymmState_isNormalized ψ hψ), ev_one_of_isNormalized ψ hψ]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          ((qBipartiteMatchMass ψ PA.toSubMeas
              (ProjMeas.postprocess LB f).toSubMeas +
            qBipartiteMatchMass ψ (ProjMeas.postprocess LA f).toSubMeas
              PB.toSubMeas) / 2) := by
            rw [qBipartiteMatchMass_roleRegister_point_postprocessedLine_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ PA.toSubMeas
              (ProjMeas.postprocess LB f).toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ (ProjMeas.postprocess LA f).toSubMeas
              PB.toSubMeas)) / 2 := by
            ring
    _ = (qBipartiteConsDefect ψ PA.toSubMeas
            (ProjMeas.postprocess LB f).toSubMeas +
          qBipartiteConsDefect ψ (ProjMeas.postprocess LA f).toSubMeas
            PB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ PA.toMeasurement
              (ProjMeas.postprocess LB f).toMeasurement]
            rw [← qBipartiteConsDefect_of_measurements ψ
              (ProjMeas.postprocess LA f).toMeasurement PB.toMeasurement]









private lemma axisParallel_roleRegister_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (strategy : ProjStrat params ιA ιB) (s : AxisParallelTestSample params) :
    qBipartiteConsDefect (strategy.roleRegisterSymmStrategy.state)
        (axisParallelPointAnswerFamily strategy.roleRegisterSymmStrategy s)
        (axisParallelLineAnswerFamily strategy.roleRegisterSymmStrategy s) =
      (qBipartiteConsDefect strategy.state
          (axisParallelPointAnswerFamilyA strategy s)
          (axisParallelLineAnswerFamilyB strategy s) +
        qBipartiteConsDefect strategy.state
          (axisParallelLineAnswerFamilyA strategy s)
          (axisParallelPointAnswerFamilyB strategy s)) / 2 := by
  let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
  have h := qBipartiteConsDefect_roleRegister_point_postprocessedLine_eq_average
    strategy.state strategy.isNormalized
    (strategy.pointMeasurementA s.1) (strategy.pointMeasurementB s.1)
    (strategy.axisParallelMeasurementA ℓ) (strategy.axisParallelMeasurementB ℓ)
    (fun p : AxisLinePolynomial params => p zeroCoord)
  simpa [SymStrat.axisParallelFailureProbability, roleRegisterSymmStrategy,
    axisParallelPointAnswerFamily, axisParallelLineAnswerFamily,
    axisParallelPointAnswerFamilyOf, axisParallelLineAnswerFamilyOf,
    roleRegisterPointMeasurement, roleRegisterAxisParallelMeasurement,
    axisParallelPointAnswerFamilyA, axisParallelPointAnswerFamilyB,
    axisParallelLineAnswerFamilyA, axisParallelLineAnswerFamilyB, ℓ,
    ProjMeas.postprocess_toSubMeas, add_comm] using h








end ProjStrat

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Role-Register Averaging: Branch Equalities

This module proves the role-register branch equalities for heterogeneous
projective strategies.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open MIPStarRE.Quantum

open LIDT.MIPStarRE.LDT.ProjStrat

theorem solution
    {params : _root_.LIDT.MIPStarRE.LDT.Parameters} [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : _root_.LIDT.MIPStarRE.LDT.ProjStrat params ιA ιB) :
    (strategy.roleRegisterSymmStrategy).axisParallelFailureProbability =
      strategy.axisParallelRoleAverage := by
  have : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  have : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  let axParDist := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample params)
  let symmErr : _root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample params → _root_.LIDT.MIPStarRE.LDT.Error := fun s =>
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (strategy.roleRegisterSymmStrategy.state)
      (_root_.LIDT.MIPStarRE.LDT.axisParallelPointAnswerFamily strategy.roleRegisterSymmStrategy s)
      (_root_.LIDT.MIPStarRE.LDT.axisParallelLineAnswerFamily strategy.roleRegisterSymmStrategy s)
  let pointLeftLineRight : _root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample params → _root_.LIDT.MIPStarRE.LDT.Error := fun s =>
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
      (_root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelPointAnswerFamilyA strategy s)
      (_root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelLineAnswerFamilyB strategy s)
  let lineLeftPointRight : _root_.LIDT.MIPStarRE.LDT.AxisParallelTestSample params → _root_.LIDT.MIPStarRE.LDT.Error := fun s =>
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
      (_root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelLineAnswerFamilyA strategy s)
      (_root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelPointAnswerFamilyB strategy s)
  have hcongr :
      _root_.LIDT.MIPStarRE.LDT.avgOver axParDist symmErr =
        _root_.LIDT.MIPStarRE.LDT.avgOver axParDist (fun s => (pointLeftLineRight s + lineLeftPointRight s) / 2) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro s
    exact axisParallel_roleRegister_sample_eq_average strategy s
  calc
    (strategy.roleRegisterSymmStrategy).axisParallelFailureProbability
      = _root_.LIDT.MIPStarRE.LDT.avgOver axParDist symmErr := by
          rfl
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver axParDist (fun s => (pointLeftLineRight s + lineLeftPointRight s) / 2) :=
          hcongr
    _ = (_root_.LIDT.MIPStarRE.LDT.avgOver axParDist pointLeftLineRight +
          _root_.LIDT.MIPStarRE.LDT.avgOver axParDist lineLeftPointRight) / 2 := by
          rw [show (fun s => (pointLeftLineRight s + lineLeftPointRight s) / 2) =
              fun s => (1 / 2 : _root_.LIDT.MIPStarRE.LDT.Error) * (pointLeftLineRight s + lineLeftPointRight s) by
            funext s
            ring]
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_mul, _root_.LIDT.MIPStarRE.LDT.avgOver_add]
          ring
    _ = strategy.axisParallelRoleAverage := by
          unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelRoleAverage
          unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelPointLeftLineRightFailureProbability
          unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelLineLeftPointRightFailureProbability
          change (_root_.LIDT.MIPStarRE.LDT.avgOver axParDist pointLeftLineRight +
              _root_.LIDT.MIPStarRE.LDT.avgOver axParDist lineLeftPointRight) / 2 =
            (_root_.LIDT.MIPStarRE.LDT.avgOver axParDist lineLeftPointRight +
              _root_.LIDT.MIPStarRE.LDT.avgOver axParDist pointLeftLineRight) / 2
          ring
