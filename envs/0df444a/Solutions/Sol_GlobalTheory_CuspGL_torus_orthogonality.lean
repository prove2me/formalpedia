-- Prove2me | solution 1 for GlobalTheory.CuspGL.torus_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:22:01.220043+00:00
-- url     : https://prove2.me/submissions/3478d9ec-40d8-4488-9ac7-951ccc9a646c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusCharacterOrthogonality
import Theorems.Thm_GlobalTheory_CuspGL_finsum_rootsOfUnity_pow_mul_star

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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → (∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (Nat.card F ^ n - 1) ∧ IsPrimitiveRoot (θ ζ) (Nat.card F ^ n - 1)) ∧ ∀ k l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, θ α ^ k * star (θ α ^ l) = if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  intro F _ _ θ hθ n hn
  classical
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqF : ((Nat.card F : ℕ) : F) = 0 := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero F
  set q := Nat.card F with hqdef
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
  set N := q ^ n - 1 with hNdef
  have hN : 0 < N := by omega

  have hNF : (N : F) ≠ 0 := by
    intro h
    have h1 : ((N + 1 : ℕ) : F) = 0 := by
      rw [show N + 1 = q ^ n by omega, Nat.cast_pow, hqF, zero_pow hn.ne']
    rw [Nat.cast_add, h, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1
  have : NeZero (N : F) := ⟨hNF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'

  have hω : IsPrimitiveRoot (θ ζ) N :=
    ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl =>
      hζ.dvd_of_pow_eq_one l (hθ _ _ (pow_ne_zero _ hζ0) one_ne_zero (by rw [map_pow, hl, map_one]))⟩
  exact ⟨⟨ζ, hζ, hω⟩, fun k l => finsum_rootsOfUnity_pow_mul_star θ hN hζ hω k l⟩
end GlobalTheory.CuspGL
