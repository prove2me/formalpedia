-- Prove2me | solution 1 for GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:03:29.744472+00:00
-- url     : https://prove2.me/submissions/d778385b-980d-4a7d-b611-d33c2cdbd841

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Theorems.Thm_GlobalTheory_CuspGL_exists_algEquiv_pow_card_pow
import Theorems.Thm_GlobalTheory_T_invertibleEndInnerProduct_rootPowerSum_eq_torusSum


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
theorem _root_.solution (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ) (hc : IsClassFn φ)
    (hp : IsPrimitive φ) (hn : 0 < Module.finrank F V) (k l i : ℕ)
    (h : k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)]) :
    ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) =
      ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_algEquiv_pow_card_pow F i
  rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn k, GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn l]
  set N := Nat.card F ^ Module.finrank F V - 1 with hN
  have hmem : ∀ α : AlgebraicClosure F, α ^ N = 1 ↔ σ α ^ N = 1 := by
    intro α
    rw [← map_pow]
    exact ⟨fun h => by rw [h, map_one], fun h => σ.injective (by rw [h, map_one])⟩
  have hbij : Set.BijOn σ {α : AlgebraicClosure F | α ^ N = 1} {α : AlgebraicClosure F | α ^ N = 1} := by
    refine ⟨fun α hα => (hmem α).1 hα, σ.injective.injOn, fun β hβ => ⟨σ.symm β, ?_, σ.apply_symm_apply β⟩⟩
    show (σ.symm β) ^ N = 1
    rw [hmem, σ.apply_symm_apply]
    exact hβ
  refine (finsum_mem_eq_of_bijOn σ hbij fun α hα => ?_).symm
  have hα' : α ^ N = 1 := hα
  have hm : minpoly F (σ α) = minpoly F α := minpoly.algEquiv_eq σ α
  have hθ : θ α ^ N = 1 := by rw [← map_pow, hα', map_one]
  have key : ∀ a : ℕ, θ α ^ a = θ α ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hθ, one_pow, mul_one]
  have hpow : θ α ^ (Nat.card F ^ i * k) = θ α ^ l := by
    rw [key, key l, mul_comm]
    exact congrArg _ h
  rw [hm, hσ, map_pow, ← pow_mul, hpow]
end GlobalTheory.CuspGL
