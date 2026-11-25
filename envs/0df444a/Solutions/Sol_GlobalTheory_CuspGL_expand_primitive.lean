-- Prove2me | solution 1 for GlobalTheory.CuspGL.expand_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:59.853864+00:00
-- url     : https://prove2.me/submissions/a82a22af-0975-41fa-a798-2705ec46d7e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobiusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfFinsumMulStarPowEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveClassFunctionExpansionRootSums
import Theorems.Thm_GlobalTheory_CuspGL_finsum_mem_mul_sub_sum
import Theorems.Thm_GlobalTheory_CuspGL_sum_mul_card_filter_modEq
import Theorems.Thm_GlobalTheory_CuspGL_eq_zero_of_ipGL_rootSum_eq_zero
import Theorems.Thm_GlobalTheory_CuspGL_psi_conj
import Theorems.Thm_GlobalTheory_CuspGL_rootSum_isAdditive_and_pow_X_sub_one
import Theorems.Thm_GlobalTheory_T_innerProduct_rootPowerSum_eq_of_frobenius_modEq
import Theorems.Thm_GlobalTheory_T_invertibleEndInnerProduct_rootPowerSum_mobius
import Theorems.Thm_GlobalTheory_T_isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse


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
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (φ : Module.End F V → ℂ)
    (hc : IsClassFn φ) (hp : IsPrimitive φ) (hn : 0 < Module.finrank F V)
    (g : Module.End F V) (hg : IsUnit g) :
    glCard F (Module.finrank F V) * (Module.finrank F V : ℂ) * φ g =
      ∑ k ∈ Finset.range (Nat.card F ^ Module.finrank F V - 1),
        ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) * psi (rootSum θ k) V g := by
  classical
  have : Finite (Module.End F V) := Module.finite_of_finite F
  set n := Module.finrank F V with hn_def
  set T := Finset.range (Nat.card F ^ n - 1) with hT
  set R : ℕ → Module.End F V → ℂ := fun k g => rootSum θ k (LinearMap.charpoly g) with hR
  set a : ℕ → ℂ := fun k => ipGL φ (R k) with ha
  set ψ : ℕ → Module.End F V → ℂ := fun k => psi (rootSum θ k) V with hψ
  set c : ℂ := glCard F n * (n : ℂ) with hc_def
  set D : Module.End F V → ℂ := fun x => c * φ x - ∑ k ∈ T, a k * ψ k x with hD
  have hDc : IsClassFn D := by
    intro e x
    simp only [hD, hψ]
    rw [hc e x]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [psi_conj F (rootSum θ k) V V e x]
  have hDp : IsPrimitive D := by
    intro A h1 h2 x hx
    have := finsum_mem_mul_sub_sum (nilRad A) c (fun y => φ (x + y)) T a (fun k y => ψ k (x + y))
    simp only [hD]
    rw [this, hp A h1 h2 x hx]
    have hz : ∀ k, ∑ᶠ y ∈ nilRad A, ψ k (x + y) = 0 := fun k =>
      GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V (rootSum θ k) (rootSum_isAdditive_and_pow_X_sub_one F θ k).1 A h1 h2 x hx
    simp [hz]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have horth : ∀ l, ipGL D (fun x : Module.End F V => rootSum θ l (LinearMap.charpoly x)) = 0 := by
    intro l
    have hexp : ∀ x, D x * star (R l x) = c * (φ x * star (R l x)) - ∑ k ∈ T, a k * (ψ k x * star (R l x)) := by
      intro x
      simp only [hD, sub_mul, Finset.sum_mul, mul_assoc]
    have hsum := finsum_mem_mul_sub_sum {x : Module.End F V | IsUnit x} c (fun x => φ x * star (R l x)) T a
      (fun k x => ψ k x * star (R l x))
    have h30342 : ∀ k, ipGL (ψ k) (R l) = glCard F n *
        (((Finset.range n).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ n - 1)])).card : ℂ) :=
      fun k => GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn k l
    have hA : ∀ k i : ℕ, k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ n - 1)] → a k = a l :=
      fun k i hki => GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq F V θ φ hc hp hn k l i hki
    have hmain := sum_mul_card_filter_modEq (Nat.card F) n l hq hn a hA
    show ∑ᶠ x ∈ {x : Module.End F V | IsUnit x}, D x * star (R l x) = 0
    simp only [hexp]
    rw [hsum]
    have e1 : ∑ᶠ x ∈ {x : Module.End F V | IsUnit x}, φ x * star (R l x) = a l := rfl
    have e2 : ∀ k, ∑ᶠ x ∈ {x : Module.End F V | IsUnit x}, ψ k x * star (R l x) = ipGL (ψ k) (R l) :=
      fun k => rfl
    simp only [e1, e2, h30342]
    have e3 : ∑ k ∈ T, a k * (glCard F n *
        (((Finset.range n).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ n - 1)])).card : ℂ)) =
        glCard F n * ∑ k ∈ T, a k *
        (((Finset.range n).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ n - 1)])).card : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e3, hT, hmain, hc_def]
    ring
  have hz := eq_zero_of_ipGL_rootSum_eq_zero F V θ hθ D hDc hDp hn horth g hg
  simp only [hD] at hz
  exact sub_eq_zero.mp hz
end GlobalTheory.CuspGL
