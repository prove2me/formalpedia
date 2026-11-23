-- Prove2me | solution 1 for GlobalTheory.ddChar_unip_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:00.626991+00:00
-- url     : https://prove2.me/submissions/96cf7a82-22a0-47a3-980b-e299f2829b7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]
namespace GlobalTheory
theorem _root_.solution (ψ : GL n R →* A) (N : Matrix n n R) (hN : N * N = 0) (d : GL n R)
    (p q : R) (hp : (d : Matrix n n R) * N = p • N) (hq : N * (d : Matrix n n R) = q • N)
    (hpq : IsUnit (q - p)) : ψ (ddCharUnip N hN) = 1 := by
  obtain ⟨c, hc⟩ := hpq
  set M : Matrix n n R := ((c⁻¹ : Rˣ) : R) • N with hM
  have hM2 : M * M = 0 := by
    rw [hM, Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero, smul_zero]
  have hMM : ∀ a : R, (a • M) * (a • M) = 0 := fun a => by
    rw [Matrix.smul_mul, Matrix.mul_smul, hM2, smul_zero, smul_zero]
  have hdM : (d : Matrix n n R) * M = p • M := by rw [hM, Matrix.mul_smul, hp, smul_comm]
  have hMd : M * (d : Matrix n n R) = q • M := by rw [hM, Matrix.smul_mul, hq, smul_comm]
  clear_value M
  let U : R → GL n R := fun a => ddCharUnip (a • M) (hMM a)
  have hU_add : ∀ a b : R, U a * U b = U (a + b) := by
    intro a b
    apply Units.ext
    show (1 + a • M) * (1 + b • M) = 1 + (a + b) • M
    have h0 : (a • M) * (b • M) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hM2, smul_zero, smul_zero]
    simp only [add_mul, mul_add, one_mul, mul_one, h0, add_zero, add_smul]
    abel
  have hconj : d * U q = U p * d := by
    apply Units.ext
    show (d : Matrix n n R) * (1 + q • M) = (1 + p • M) * (d : Matrix n n R)
    rw [mul_add, mul_one, add_mul, one_mul, Matrix.mul_smul, hdM, Matrix.smul_mul, hMd,
      smul_smul, smul_smul, mul_comm q p]
  have h1 : ψ (U q) = ψ (U p) := by
    have := congrArg ψ hconj
    rw [map_mul, map_mul, mul_comm (ψ (U p))] at this
    exact mul_left_cancel this
  have h2 : U q = U p * U (q - p) := by rw [hU_add, add_sub_cancel]
  have h3 : ψ (U (q - p)) = 1 := by
    have := congrArg ψ h2
    rw [map_mul, h1] at this
    exact mul_left_cancel (this.symm.trans (mul_one _).symm)
  have h4 : U (q - p) = ddCharUnip N hN := by
    apply Units.ext
    show 1 + (q - p) • M = 1 + N
    rw [hM, smul_smul, ← hc, Units.mul_inv, one_smul]
  rw [← h4]
  exact h3
end GlobalTheory
