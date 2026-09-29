-- Prove2me | solution 1 for LocalGL2.unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/acbec263-2c3e-5ef3-8153-67b99ed54180

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open LocalGL2 HeckePair

namespace R5UnipCartan

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

theorem coe_z :
    ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.val_mul, coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_z_pow (n : ℕ) :
    (((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K ϖ ^ n • (1 : Matrix (Fin 2) (Fin 2) K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, coe_z, smul_mul_smul_comm, one_mul, ← pow_succ]

theorem coe_localRepInf_pow (n : ℕ) :
    ((localRepInf ϖ hϖ0 ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, algebraMap R K ϖ ^ n] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, coe_localRepInf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem z_central (g : GL (Fin 2) K) :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g = g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) := by
  apply Units.ext
  have h := coe_z ϖ hϖ0
  rw [Units.val_mul] at h
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, h, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

theorem commute_diagPi_localRepInf : Commute (diagPi ϖ hϖ0) (localRepInf ϖ hϖ0 : GL (Fin 2) K) := by
  show diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 = localRepInf ϖ hϖ0 * diagPi ϖ hϖ0
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, coe_diagPi, coe_localRepInf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem zpow_neg_mul_zpow_eq (r : ℕ) :
    diagPi ϖ hϖ0 ^ (-(r : ℤ)) * localRepInf ϖ hϖ0 ^ (r : ℤ) =
      (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (-(r : ℤ)) * localRepInf ϖ hϖ0 ^ (2 * r) := by
  rw [(commute_diagPi_localRepInf ϖ hϖ0).mul_zpow, mul_assoc, ← zpow_natCast, ← zpow_add]
  congr 2
  push_cast
  ring

theorem mem_doubleCoset_central_mul_iff {G : Type*} [Group G] {U : Subgroup G} {c g x : G}
    (hc : ∀ y : G, c * y = y * c) :
    x ∈ doubleCoset U (c * g) ↔ c⁻¹ * x ∈ doubleCoset U g := by
  rw [mem_doubleCoset_iff, mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    refine ⟨u, hu, v, hv, ?_⟩
    rw [show u * (c * g) * v = c * (u * g * v) by rw [← mul_assoc, ← hc u]; group]
    rw [inv_mul_cancel_left]
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨u, hu, v, hv, ?_⟩
    rw [show u * (c * g) * v = c * (u * g * v) by rw [← mul_assoc, ← hc u]; group, huv,
      mul_inv_cancel_left]

def lowerR (c : R) : GL (Fin 2) R :=
  ⟨!![1, 0; c, 1], !![1, 0; -c, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def rightR (u : Rˣ) (t : R) : GL (Fin 2) R :=
  ⟨!![t, (u : R); -((u⁻¹ : Rˣ) : R), 0], !![0, -(u : R); ((u⁻¹ : Rˣ) : R), t], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]⟩

theorem key (u : Rˣ) (r : ℕ) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (lowerR (((u⁻¹ : Rˣ) : R) * ϖ ^ r)) *
        localRepInf ϖ hϖ0 ^ (2 * r) *
        Matrix.GeneralLinearGroup.map (algebraMap R K) (rightR u (ϖ ^ r)) =
      (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ r *
        AutomorphicForm.unipotentGL2 (algebraMap R K u * ((algebraMap R K ϖ)⁻¹) ^ r) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hu0 : algebraMap R K u ≠ 0 := (Units.map (algebraMap R K : R →* K) u).ne_zero
  simp only [Units.val_mul, coe_z_pow, coe_localRepInf_pow, AutomorphicForm.unipotentGL2_coe,
    Matrix.smul_mul, Matrix.one_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lowerR, rightR, map_mul, map_pow, map_neg] <;>
    field_simp <;> ring

theorem unipotentGL2_algebraMap_mem (b : R) :
    AutomorphicForm.unipotentGL2 (algebraMap R K b) ∈ integralSubgroup R K := by
  refine ⟨AutomorphicForm.unipotentGL2 b, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.map_apply, AutomorphicForm.unipotentGL2_coe, AutomorphicForm.unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem integral_case (b : R) :
    AutomorphicForm.unipotentGL2 (algebraMap R K b) ∈
      doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ (0 : ℤ) * localRepInf ϖ hϖ0 ^ (0 : ℤ)) := by
  rw [zpow_zero, zpow_zero, mul_one]
  exact mem_doubleCoset_iff.mpr ⟨_, unipotentGL2_algebraMap_mem b, 1, one_mem _, by rw [mul_one, mul_one]⟩

theorem polar_case (u : Rˣ) (r : ℕ) :
    AutomorphicForm.unipotentGL2 (algebraMap R K u * ((algebraMap R K ϖ)⁻¹) ^ r) ∈
      doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ (-(r : ℤ)) * localRepInf ϖ hϖ0 ^ (r : ℤ)) := by
  have hc : ∀ y : GL (Fin 2) K, (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (-(r : ℤ)) * y =
      y * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (-(r : ℤ)) := fun y =>
    (Commute.zpow_left (show Commute (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) y from z_central ϖ hϖ0 y) _).eq
  rw [zpow_neg_mul_zpow_eq, mem_doubleCoset_central_mul_iff hc, zpow_neg, inv_inv, zpow_natCast, ← key]
  exact mem_doubleCoset_iff.mpr ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩

end R5UnipCartan

open R5UnipCartan in
theorem solution
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) :
    (∀ b : R, AutomorphicForm.unipotentGL2 (algebraMap R K b) ∈
        HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
          (LocalGL2.diagPi ϖ hϖ0 ^ (0 : ℤ) * LocalGL2.localRepInf ϖ hϖ0 ^ (0 : ℤ))) ∧
    ∀ (u : Rˣ) (r : ℕ),
      AutomorphicForm.unipotentGL2 (algebraMap R K u * ((algebraMap R K ϖ)⁻¹) ^ r) ∈
        HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
          (LocalGL2.diagPi ϖ hϖ0 ^ (-(r : ℤ)) * LocalGL2.localRepInf ϖ hϖ0 ^ (r : ℤ)) :=
  ⟨integral_case ϖ hϖ0, polar_case ϖ hϖ0⟩

end S_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow
end P2MW
export P2MW.S_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow (solution)
