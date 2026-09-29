-- Prove2me | solution 1 for NumberField.LevelArith.kummerChar_mul_and_add_and_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bc8e0bd6-9647-53ec-a665-b786605cb678

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

namespace P2MW.S_NumberField_LevelArith_kummerChar_mul_and_add_and_level

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

theorem solution
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F) :
    (∀ (x : (↥F)ˣ) (σ τ : ↥F.fixingSubgroup), kummerChar p ζ hζ F x (σ * τ) = kummerChar p ζ hζ F x σ + kummerChar p ζ hζ F x τ) ∧
    (∀ (x x' : (↥F)ˣ) (σ : ↥F.fixingSubgroup), kummerChar p ζ hζ F (x * x') σ = kummerChar p ζ hζ F x σ + kummerChar p ζ hζ F x' σ) ∧
    (∀ (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup),
      (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ (F ⊔ IntermediateField.adjoin ℚ {kummerRoot p F x}).fixingSubgroup → kummerChar p ζ hζ F x σ = 0) := by
  have hy0 := kummerRoot_ne_zero p F
  refine ⟨fun x σ τ => ?_, fun x x' σ => ?_, fun x σ hσ => ?_⟩
  ·
    apply CycBaseKummer.eq_of_pow_val_eq p ζ hζ
    have h := kummerChar_spec p ζ hζ F x (σ * τ)
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply, kummerChar_spec p ζ hζ F x τ, map_mul, map_pow,
      CycBaseKummer.apply_eq_of_mem F σ.2 hζF, kummerChar_spec p ζ hζ F x σ, ← mul_assoc,
      mul_comm (ζ ^ _) (ζ ^ _)] at h
    rw [CycBaseKummer.pow_val_add p ζ hζ]
    exact (mul_right_cancel₀ (hy0 x) h).symm
  ·
    apply CycBaseKummer.eq_of_pow_val_eq p ζ hζ
    have hx0 : ∀ z : (↥F)ˣ, ((z : ↥F) : AlgebraicClosure ℚ) ≠ 0 := fun z => by
      rw [← kummerRoot_pow p F z]; exact pow_ne_zero _ (hy0 z)
    have hyy : kummerRoot p F x * kummerRoot p F x' ≠ 0 := mul_ne_zero (hy0 x) (hy0 x')
    have hε : (kummerRoot p F (x * x') / (kummerRoot p F x * kummerRoot p F x')) ^ p = 1 := by
      rw [div_pow, mul_pow, kummerRoot_pow, kummerRoot_pow, kummerRoot_pow, Units.val_mul, MulMemClass.coe_mul,
        div_self (mul_ne_zero (hx0 x) (hx0 x'))]
    have hσε := CycBaseKummer.apply_eq_of_mem F σ.2 (CycBaseKummer.mem_of_pow_eq_one p ζ hζ F hζF hε)
    have h1 : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F (x * x')) =
        ζ ^ (kummerChar p ζ hζ F x σ).val * ζ ^ (kummerChar p ζ hζ F x' σ).val * kummerRoot p F (x * x') := by
      have h2 : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F (x * x')) =
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (kummerRoot p F (x * x') / (kummerRoot p F x * kummerRoot p F x') * (kummerRoot p F x * kummerRoot p F x')) := by
        rw [div_mul_cancel₀ _ hyy]
      rw [h2, map_mul, map_mul, hσε, kummerChar_spec p ζ hζ F x σ, kummerChar_spec p ζ hζ F x' σ]
      conv_rhs => rw [← div_mul_cancel₀ (kummerRoot p F (x * x')) hyy]
      ring
    have h := kummerChar_spec p ζ hζ F (x * x') σ
    rw [CycBaseKummer.pow_val_add p ζ hζ]
    exact mul_right_cancel₀ (hy0 _) (h.symm.trans h1)
  ·
    apply CycBaseKummer.kummerChar_eq_zero_of_apply_eq p ζ hζ F x σ
    have hy : kummerRoot p F x ∈ F ⊔ IntermediateField.adjoin ℚ {kummerRoot p F x} :=
      (le_sup_right : IntermediateField.adjoin ℚ {kummerRoot p F x} ≤ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
    exact CycBaseKummer.apply_eq_of_mem _ hσ hy

end S_NumberField_LevelArith_kummerChar_mul_and_add_and_level
end P2MW
export P2MW.S_NumberField_LevelArith_kummerChar_mul_and_add_and_level (solution)
