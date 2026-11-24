-- Prove2me | solution 1 for GlobalTheory.CuspGL.torus_fourier_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:10.497823+00:00
-- url     : https://prove2.me/submissions/fdfb7c18-82dc-479f-8865-171e3f3bc84e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfFinsumMulStarPowEqZero
import Theorems.Thm_GlobalTheory_CuspGL_eq_zero_of_finsum_mul_star_pow_eq_zero

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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → ∀ c : AlgebraicClosure F → ℂ, (∀ l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α * star (θ α ^ l) = 0) → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α = 0 := by
  intro F _ _ θ hθ n hn c h
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hN : 0 < Nat.card F ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' hq)
  exact eq_zero_of_finsum_mul_star_pow_eq_zero θ hθ _ hN c h
end GlobalTheory.CuspGL
