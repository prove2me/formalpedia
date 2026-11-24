-- Prove2me | solution 1 for GlobalTheory.CuspGL.isChar_brauerLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:18.193555+00:00
-- url     : https://prove2.me/submissions/f290c749-3c56-45be-a80d-cc262db10339

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisAbelianByPrimePowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_TraceLiftMonomialMatrixEqSumEigenvaluesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterBrauerLiftAbelianByPrimePower
import Theorems.Thm_GlobalTheory_CuspGL_basis_smul_eq_smul_cancel
import Theorems.Thm_GlobalTheory_T_exists_monomial_basis_abelianByPrimePower
import Theorems.Thm_GlobalTheory_T_trace_lift_monomialMatrix_eq_sum_eigenvalues


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (G : Type) [Group G] [Finite G], AbByP G → (Nat.card G : k) ≠ 0 → ∀ (n : ℕ) (ρ : G →* GL (Fin n) k), IsChar ℂ ℂ (fun g => ((Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) k)).roots.map θ).sum) := by
  intro k _ _ θ hθ G _ _ hG hc n ρ
  classical
  let R : Representation k G (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _).toMonoidHom.comp
      (Units.coeHom _)).comp ρ
  have hR : ∀ g, R g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k) := fun g => rfl
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_monomial_basis_abelianByPrimePower k G (Fin n → k) R hG hc
  choose s c hsc using hb
  have hc0 : ∀ g i, c g i ≠ 0 := by
    intro g i h0
    have h1 : R g (b i) = 0 := by rw [hsc, h0, zero_smul]
    have h2 : R (g⁻¹ * g) (b i) = 0 := by
      rw [map_mul, Module.End.mul_apply, h1, map_zero]
    rw [inv_mul_cancel, map_one, Module.End.one_apply] at h2
    exact b.ne_zero i h2
  have hmul : ∀ g h i, s (g * h) i = s g (s h i) ∧ c (g * h) i = c g (s h i) * c h i := by
    intro g h i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_mul, Module.End.mul_apply, hsc, map_smul, hsc, smul_smul, mul_comm]
  have hone : ∀ i, s 1 i = i ∧ c 1 i = 1 := by
    intro i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_one, Module.End.one_apply, one_smul]
  let σ : G → Equiv.Perm (Fin m) := fun g =>
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun i => by rw [← (hmul _ _ _).1, inv_mul_cancel, (hone i).1]
      right_inv := fun i => by rw [← (hmul _ _ _).1, mul_inv_cancel, (hone i).1] }
  let L : G →* Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun g => Matrix.of fun i j => if i = σ g j then θ (c g j) else 0
      map_one' := by
        ext i j
        simp [σ, (hone j).1, (hone j).2, Matrix.one_apply]
      map_mul' := by
        intro g h
        ext i j
        simp [σ, Matrix.mul_apply, (hmul g h j).1, (hmul g h j).2] }
  have hM : ∀ g, (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      = LinearMap.toMatrix b b (R g) := by
    intro g
    ext i j
    simp [σ, LinearMap.toMatrix_apply, hsc, Finsupp.single_apply, eq_comm]
  refine ⟨m, (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ℂ ≃ₐ[ℂ] _).toMonoidHom.comp L, fun g => ?_⟩
  have h1 : (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      ^ Nat.card G = 1 := by
    rw [hM, LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one', map_one, LinearMap.toMatrix_one]
  have h2 : L g ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have h3 := GlobalTheory.T.trace_lift_monomialMatrix_eq_sum_eigenvalues k θ hθ m (Nat.card G) (σ g) (c g) (hc0 g) hc h1 h2
  rw [hM, LinearMap.charpoly_toMatrix, hR, Matrix.charpoly_toLin'] at h3
  show _ = LinearMap.trace ℂ _ (Matrix.toLin' (L g))
  rw [Matrix.trace_toLin'_eq]
  exact h3.symm
end GlobalTheory.CuspGL
