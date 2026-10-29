-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_is_good_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:23:18.422271+00:00
-- url     : https://prove2.me/submissions/8c742e69-0e38-4e0d-a3b6-34516eb77bdf

-- Generated proof for MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_is_good_three_mul.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_axisParallelRoleAverage_nonneg
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_diagonalRoleAverage_nonneg
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_lowIndividualDegreeFailureProbability_eq_role_averages
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_roleRegisterSymmStrategy_axisParallel_eq_roleAverage
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_roleRegisterSymmStrategy_diagonal_eq_roleAverage
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



private lemma ev_roleRegisterSymmState_roleRegisterProjMeas_outcome
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA NA : ProjMeas Outcome ιA) (MB NB : ProjMeas Outcome ιB)
    (a : Outcome) :
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas MA MB).outcome a)
          ((roleRegisterProjMeas NA NB).outcome a)) =
      (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
        (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
  let fillerA : ProjMeas Outcome ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerB : ProjMeas Outcome ιB := ProjMeas.trivialDistinguishedOutcome default
  calc
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas MA MB).outcome a)
          ((roleRegisterProjMeas NA NB).outcome a))
      = ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (NA.outcome a) (fillerB.outcome a))) +
            rolePairDirectSumCond Role.A Role.B
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (fillerA.outcome a) (NB.outcome a))) +
              (rolePairDirectSumCond Role.B Role.A
                (opTensor
                  (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                  (localDirectSumBlock (NA.outcome a) (fillerB.outcome a))) +
                rolePairDirectSumCond Role.B Role.B
                  (opTensor
                    (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                    (localDirectSumBlock (fillerA.outcome a) (NB.outcome a))))) := by
          congr 1
          simp [roleRegisterProjMeas, opTensor_roleBlock_eq_rolePairDirectSumCond_sum,
            fillerA, fillerB]
    _ =
        ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (NA.outcome a) (fillerB.outcome a)))) +
          ev (roleRegisterSymmState ψ)
            (rolePairDirectSumCond Role.A Role.B
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (fillerA.outcome a) (NB.outcome a)))) +
            (ev (roleRegisterSymmState ψ)
              (rolePairDirectSumCond Role.B Role.A
                (opTensor
                  (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                  (localDirectSumBlock (NA.outcome a) (fillerB.outcome a)))) +
              ev (roleRegisterSymmState ψ)
                (rolePairDirectSumCond Role.B Role.B
                  (opTensor
                    (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                    (localDirectSumBlock (fillerA.outcome a) (NB.outcome a))))) := by
          repeat rw [ev_add]
    _ = 0 +
          (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            ((1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) +
              0) := by
          rw [ev_roleRegisterSymmState_rolePairDirectSumCond_AA,
            ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePairDirectSumCond_BB]
    _ = (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
        (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
          ring









private lemma qBipartiteMatchMass_roleRegisterProjMeas_eq_average
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA NA : ProjMeas Outcome ιA) (MB NB : ProjMeas Outcome ιB) :
    qBipartiteMatchMass (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
        (roleRegisterProjMeas NA NB).toSubMeas =
      (qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome,
        ev (roleRegisterSymmState ψ)
          (opTensor ((roleRegisterProjMeas MA MB).outcome a)
            ((roleRegisterProjMeas NA NB).outcome a))
      = ∑ a : Outcome,
          ((1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact ev_roleRegisterSymmState_roleRegisterProjMeas_outcome ψ MA NA MB NB a
    _ = (1 / 2 : Error) *
          ∑ a : Outcome, ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
        (1 / 2 : Error) *
          ∑ a : Outcome, ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ =
        (∑ a : Outcome, ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
          ∑ a : Outcome, ev ψ (opTensor (NA.outcome a) (MB.outcome a))) / 2 := by
          ring

private lemma qBipartiteConsDefect_roleRegisterProjMeas_eq_average
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA NA : ProjMeas Outcome ιA) (MB NB : ProjMeas Outcome ιB) :
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
        (roleRegisterProjMeas NA NB).toSubMeas =
      (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
        (roleRegisterProjMeas NA NB).toSubMeas
      = ev (roleRegisterSymmState ψ)
          (1 : MIPStarRE.Quantum.Op
            (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas MA MB).toSubMeas
            (roleRegisterProjMeas NA NB).toSubMeas := by
            exact qBipartiteConsDefect_of_measurements (roleRegisterSymmState ψ)
              (roleRegisterProjMeas MA MB).toMeasurement
              (roleRegisterProjMeas NA NB).toMeasurement
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas MA MB).toSubMeas
            (roleRegisterProjMeas NA NB).toSubMeas := by
            rw [ev_one_of_isNormalized (roleRegisterSymmState ψ)
              (roleRegisterSymmState_isNormalized ψ hψ), ev_one_of_isNormalized ψ hψ]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          ((qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2) := by
            rw [qBipartiteMatchMass_roleRegisterProjMeas_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas)) / 2 := by
            ring
    _ = (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
          qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ MA.toMeasurement NB.toMeasurement]
            rw [← qBipartiteConsDefect_of_measurements ψ NA.toMeasurement MB.toMeasurement]

private lemma qBipartiteSSCDefect_roleRegisterProjMeas_eq_cons
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    qBipartiteSSCDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas =
      qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas := by
  calc
    qBipartiteSSCDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
      = qBipartiteConsDefect (roleRegisterSymmState ψ)
          (roleRegisterProjMeas MA MB).toSubMeas
          (roleRegisterProjMeas MA MB).toSubMeas := by
          simp [qBipartiteSSCDefect, qBipartiteConsDefect, qBipartiteMatchMass,
            (roleRegisterProjMeas MA MB).total_eq_one, leftTensor, opTensor]
    _ = (qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas +
          qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas) / 2 := by
          rw [qBipartiteConsDefect_roleRegisterProjMeas_eq_average ψ hψ MA MA MB MB]
    _ = qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas := by
          ring

/-- The point self-consistency branch of the heterogeneous role-register
symmetrization is exactly the original cross-prover point-agreement branch. -/
theorem roleRegisterSymmStrategy_selfConsistency_eq_pointAgreement
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    (strategy.roleRegisterSymmStrategy).selfConsistencyFailureProbability =
      strategy.pointAgreementFailureProbability := by
  have : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  have : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  unfold SymStrat.selfConsistencyFailureProbability ProjStrat.pointAgreementFailureProbability
  unfold bipartiteSSCError bipartiteConsError
  refine Finset.sum_congr rfl ?_
  intro u _
  exact congrArg (fun t => (uniformDistribution (Point params)).weight u * t)
    (qBipartiteSSCDefect_roleRegisterProjMeas_eq_cons strategy.state strategy.isNormalized
      (strategy.pointMeasurementA u) (strategy.pointMeasurementB u))










end ProjStrat

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Final.lean. -/
/-!
# Role-Register Averaging: Goodness Bound

This module packages the branch equalities into the three-times-error goodness
bound for the role-register symmetric strategy.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat



/-- The point-agreement branch of a two-space projective strategy is
nonnegative. -/
theorem pointAgreementFailureProbability_nonneg
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    0 ≤ strategy.pointAgreementFailureProbability := by
  unfold ProjStrat.pointAgreementFailureProbability
  exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)










end ProjStrat

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Test/StrategyFailures.lean. -/
/-!
# Symmetrized-strategy failure probabilities and test bounds

Failure-probability surrogates and basic low-individual-degree test bounds for
the split strategy interface.
-/

@[expose] public section

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

/-! ### Symmetrized strategies and tested-branch bounds -/

namespace SymStrat









end SymStrat









/-! ### Answer-valued symmetric strategies -/









/-- If three nonnegative summands have average at most `eps`, each summand is at
most `3 * eps`. -/
lemma three_summand_bounds_of_average_le
    {axis point diagonal eps : Error}
    (haxis : 0 ≤ axis) (hpoint : 0 ≤ point) (hdiagonal : 0 ≤ diagonal)
    (hmain : (axis + point + diagonal) / 3 ≤ eps) :
    axis ≤ 3 * eps ∧ point ≤ 3 * eps ∧ diagonal ≤ 3 * eps := by
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Role-Register Averaging: Goodness Bound

This module packages the branch equalities into the three-times-error goodness
bound for the role-register symmetric strategy.
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
    {strategy : _root_.LIDT.MIPStarRE.LDT.ProjStrat params ιA ιB} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.roleRegisterSymmStrategy).IsGood (3 * eps) (3 * eps) (3 * eps) := by
  have haxis_nonneg : 0 ≤ strategy.axisParallelRoleAverage :=
    _root_.LIDT.MIPStarRE.LDT.ProjStrat.axisParallelRoleAverage_nonneg strategy
  have hpoint_nonneg : 0 ≤ strategy.pointAgreementFailureProbability :=
    _root_.LIDT.MIPStarRE.LDT.ProjStrat.pointAgreementFailureProbability_nonneg strategy
  have hdiag_nonneg : 0 ≤ strategy.diagonalRoleAverage :=
    _root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalRoleAverage_nonneg strategy
  have hmain :
      (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
        strategy.diagonalRoleAverage) / 3 ≤ eps := by
    simpa only [_root_.LIDT.MIPStarRE.LDT.ProjStrat.lowIndividualDegreeFailureProbability_eq_role_averages] using
      hpass.soundnessHypothesis
  have haxis : strategy.axisParallelRoleAverage ≤ 3 * eps :=
    (_root_.LIDT.MIPStarRE.LDT.three_summand_bounds_of_average_le
      haxis_nonneg hpoint_nonneg hdiag_nonneg hmain).1
  have hpoint : strategy.pointAgreementFailureProbability ≤ 3 * eps :=
    (_root_.LIDT.MIPStarRE.LDT.three_summand_bounds_of_average_le
      haxis_nonneg hpoint_nonneg hdiag_nonneg hmain).2.1
  have hdiag : strategy.diagonalRoleAverage ≤ 3 * eps :=
    (_root_.LIDT.MIPStarRE.LDT.three_summand_bounds_of_average_le
      haxis_nonneg hpoint_nonneg hdiag_nonneg hmain).2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_axisParallel_eq_roleAverage strategy]
    exact haxis
  · rw [_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_selfConsistency_eq_pointAgreement strategy]
    exact hpoint
  · rw [_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_diagonal_eq_roleAverage strategy]
    exact hdiag
