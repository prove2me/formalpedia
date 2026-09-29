-- Prove2me | solution 1 for NumberField.LevelArith.kummerChar_conj_eq_cycloChar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/284d954a-3fe9-524f-9131-6a0bb8a528a3

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_KummerCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_kummerChar_conj_eq_cycloChar_mul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

namespace CycBaseKummer

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)

include hζ in

lemma pow_val_add (a b : ZMod p) : ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

include hζ in

lemma eq_of_pow_val_eq {a b : ZMod p} (h : ζ ^ a.val = ζ ^ b.val) : a = b :=
  ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

include hζ in
lemma eq_zero_of_pow_val_eq_one {a : ZMod p} (h : ζ ^ a.val = 1) : a = 0 :=
  eq_of_pow_val_eq p ζ hζ (by rw [h, ZMod.val_zero, pow_zero])

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ))

lemma apply_eq_of_mem {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ F.fixingSubgroup)
    {z : AlgebraicClosure ℚ} (hz : z ∈ F) : σ z = z :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ z hz

include hζ in

lemma mem_of_pow_eq_one (hζF : ζ ∈ F) {ε : AlgebraicClosure ℚ} (hε : ε ^ p = 1) : ε ∈ F := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hε
  exact pow_mem hζF i

lemma kummerChar_eq_zero_of_apply_eq (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup)
    (h : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) = kummerRoot p F x) :
    kummerChar p ζ hζ F x σ = 0 := by
  apply eq_zero_of_pow_val_eq_one p ζ hζ
  have h2 := kummerChar_spec p ζ hζ F x σ
  rw [h] at h2

  have h3 := mul_left_eq_self₀.mp h2.symm
  exact h3.resolve_right (kummerRoot_ne_zero p F x)

end CycBaseKummer

namespace CycBaseKummer

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)

include hζ in

lemma pow_val_mul (a b : ZMod p) : ζ ^ (a * b).val = ζ ^ (a.val * b.val) := by
  rw [ZMod.val_mul]
  conv_rhs => rw [← Nat.div_add_mod (a.val * b.val) p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

include hζ in

lemma apply_eq_pow_cycloChar (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    γ ζ = ζ ^ ((cycloChar p γ : ZMod p)).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Fact.out : p.Prime).ne_zero
  have ht : Units.mk0 ζ hζ0 ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity]; apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]; exact hζ.pow_eq_one
  have h := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (γ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) ht
  rw [Units.val_mk0] at h
  exact h

end CycBaseKummer

theorem solution
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F)
    (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hγF : ∀ z ∈ F, γ z ∈ F)
    (σ : ↥F.fixingSubgroup) (hconj : γ * (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * γ⁻¹ ∈ F.fixingSubgroup)
    (x x' : (↥F)ˣ) (hx' : ((x' : ↥F) : AlgebraicClosure ℚ) = γ ((x : ↥F) : AlgebraicClosure ℚ)) :
    kummerChar p ζ hζ F x' ⟨γ * (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * γ⁻¹, hconj⟩ = ((cycloChar p γ : ZMod p)) * kummerChar p ζ hζ F x σ := by
  have hp : p.Prime := Fact.out
  apply CycBaseKummer.eq_of_pow_val_eq p ζ hζ
  have hy0 := kummerRoot_ne_zero p F x
  have hy0' := kummerRoot_ne_zero p F x'
  have hγy0 : γ (kummerRoot p F x) ≠ 0 := (map_ne_zero γ).mpr hy0
  have hγy : (γ (kummerRoot p F x)) ^ p = ((x' : ↥F) : AlgebraicClosure ℚ) := by
    rw [← map_pow, kummerRoot_pow, hx']

  have hε : (kummerRoot p F x' / γ (kummerRoot p F x)) ^ p = 1 := by
    rw [div_pow, kummerRoot_pow, hγy, div_self]
    rw [← hγy]; exact pow_ne_zero _ hγy0
  have hτε : (γ * (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * γ⁻¹) (kummerRoot p F x' / γ (kummerRoot p F x)) =
      kummerRoot p F x' / γ (kummerRoot p F x) :=
    CycBaseKummer.apply_eq_of_mem F hconj (CycBaseKummer.mem_of_pow_eq_one p ζ hζ F hζF hε)
  have h1 : (γ * (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * γ⁻¹) (kummerRoot p F x') =
      ζ ^ ((cycloChar p γ : ZMod p) * kummerChar p ζ hζ F x σ).val * kummerRoot p F x' := by
    have e1 : kummerRoot p F x' = kummerRoot p F x' / γ (kummerRoot p F x) * γ (kummerRoot p F x) :=
      (div_mul_cancel₀ _ hγy0).symm
    rw [e1, map_mul, hτε, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply,
      kummerChar_spec p ζ hζ F x σ, map_mul, map_pow, CycBaseKummer.apply_eq_pow_cycloChar p ζ hζ γ, ← pow_mul,
      CycBaseKummer.pow_val_mul p ζ hζ]
    ring
  have h2 := kummerChar_spec p ζ hζ F x' ⟨γ * (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * γ⁻¹, hconj⟩
  exact mul_right_cancel₀ hy0' (h2.symm.trans h1)

end S_NumberField_LevelArith_kummerChar_conj_eq_cycloChar_mul
end P2MW
export P2MW.S_NumberField_LevelArith_kummerChar_conj_eq_cycloChar_mul (solution)
