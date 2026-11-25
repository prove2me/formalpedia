-- Prove2me | solution 1 for GlobalTheory.Nef.local_index_scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:17.920397+00:00
-- url     : https://prove2.me/submissions/a885bbb0-8b74-46e5-af2c-c2bbfee12f99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceLocalIndexColengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceLocalIndexScaledUniformiser
import Theorems.Thm_GlobalTheory_T_functionFieldPlaceOrder_calculus
import Theorems.Thm_GlobalTheory_T_functionFieldPlace_local_index_colength
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (M : Matrix (Fin n) (Fin n) F) (d : ℕ), M.det ≠ 0 →
    (∀ i j, v.1 (M⁻¹ i j) ≤ WithZero.exp (d : ℤ)) →
    ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = n * d - ord v M.det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (d : ℤ)) → φ p = 0 →
        ∀ i, v.1 (M.mulVec p i) ≤ 1 := by
  intro k F _ _ _ _ _ hFF v n M d hM hMinv
  obtain ⟨hmul, hzpow, -, -, -, ⟨π, hπ0, hπ⟩, -⟩ := GlobalTheory.T.functionFieldPlaceOrder_calculus k F v

  have hvπ : v.1 π = WithZero.exp (-1) := by
    have hne : v.1 π ≠ 0 := by simpa using hπ0
    have : WithZero.log (v.1 π) = -1 := by
      unfold ord at hπ; omega
    rw [← this, WithZero.exp_log hne]
  set c : F := π ^ d with hcdef
  have hc0 : c ≠ 0 := pow_ne_zero _ hπ0
  have hvc : v.1 c = WithZero.exp (-(d : ℤ)) := by
    rw [hcdef, map_pow, hvπ]
    show WithZero.exp (-1) ^ d = _
    rw [← WithZero.exp_nsmul]; congr 1; simp
  set h : Matrix (Fin n) (Fin n) F := c⁻¹ • M with hhdef
  have hdet : h.det = (c⁻¹) ^ n * M.det := by rw [hhdef, Matrix.det_smul, Fintype.card_fin]
  have hdet0 : h.det ≠ 0 := by rw [hdet]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc0)) hM
  have hinv : h⁻¹ = c • M⁻¹ := by
    rw [hhdef]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM)]
  have hinvb : ∀ i j, v.1 (h⁻¹ i j) ≤ 1 := by
    intro i j
    rw [hinv, Matrix.smul_apply, smul_eq_mul, map_mul, hvc]
    calc WithZero.exp (-(d : ℤ)) * v.1 (M⁻¹ i j) ≤ WithZero.exp (-(d : ℤ)) * WithZero.exp (d : ℤ) :=
          by gcongr; exact hMinv i j
      _ = 1 := by rw [← WithZero.exp_add]; simp
  obtain ⟨N, φ₀, hN, hφ₀⟩ := GlobalTheory.T.functionFieldPlace_local_index_colength k F hFF v n h hdet0 hinvb

  have hord : ord v h.det = -(n * d : ℤ) + ord v M.det := by
    have e : (c⁻¹) ^ n = π ^ (-(n * d : ℤ)) := by
      rw [hcdef, inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
    rw [hdet, hmul _ _ (pow_ne_zero _ (inv_ne_zero hc0)) hM, e, hzpow π hπ0, hπ, mul_one]
  let sc : (Fin n → F) →ₗ[k] (Fin n → F) :=
    { toFun := fun p => c • p
      map_add' := fun p q => smul_add c p q
      map_smul' := fun a p => by
        ext i
        show c * (a • p i) = a • (c * p i)
        rw [Algebra.smul_def, Algebra.smul_def]; ring }
  refine ⟨N, φ₀ ∘ₗ sc, by rw [hN, hord]; ring, ?_⟩
  intro p hp hφ i
  have hx : ∀ i, v.1 ((c • p) i) ≤ 1 := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hvc]
    calc WithZero.exp (-(d : ℤ)) * v.1 (p i) ≤ WithZero.exp (-(d : ℤ)) * WithZero.exp (d : ℤ) :=
          by gcongr; exact hp i
      _ = 1 := by rw [← WithZero.exp_add]; simp
  have := hφ₀ (c • p) hx hφ i
  have e2 : h.mulVec (c • p) = M.mulVec p := by
    rw [hhdef, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rwa [e2] at this
end GlobalTheory.Nef
