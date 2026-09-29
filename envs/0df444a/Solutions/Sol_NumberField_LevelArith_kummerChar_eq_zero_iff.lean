-- Prove2me | solution 1 for NumberField.LevelArith.kummerChar_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1882926b-900f-54de-aa22-3b937d2df1cc

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

namespace P2MW.S_NumberField_LevelArith_kummerChar_eq_zero_iff

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

local instance CycBaseKummerKer.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance CycBaseKummerKer.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance CycBaseKummerKer.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
local instance CycBaseKummerKer.normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

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
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F) (x : (↥F)ˣ) :
    (∀ σ : ↥F.fixingSubgroup, kummerChar p ζ hζ F x σ = 0) ↔ x ∈ (powMonoidHom p : (↥F)ˣ →* (↥F)ˣ).range := by
  have hy0 := kummerRoot_ne_zero p F x
  constructor
  ·
    intro h
    have hfix : ∀ σ ∈ F.fixingSubgroup, σ (kummerRoot p F x) = kummerRoot p F x := by
      intro σ hσ
      have h2 := kummerChar_spec p ζ hζ F x ⟨σ, hσ⟩
      rw [h ⟨σ, hσ⟩, ZMod.val_zero, pow_zero, one_mul] at h2
      exact h2
    have hyF : kummerRoot p F x ∈ F := by
      have hmem : kummerRoot p F x ∈ IntermediateField.fixedField F.fixingSubgroup :=
        (IntermediateField.mem_fixedField_iff _ _).mpr hfix
      rwa [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    have hyF0 : (⟨kummerRoot p F x, hyF⟩ : ↥F) ≠ 0 := fun h0 => hy0 (congrArg Subtype.val h0)
    refine ⟨Units.mk0 _ hyF0, Units.ext (Subtype.ext ?_)⟩
    show (((Units.mk0 _ hyF0 ^ p : (↥F)ˣ) : ↥F) : AlgebraicClosure ℚ) = ((x : ↥F) : AlgebraicClosure ℚ)
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow]
    exact kummerRoot_pow p F x
  ·
    rintro ⟨z, hz⟩ σ
    apply CycBaseKummer.kummerChar_eq_zero_of_apply_eq p ζ hζ F x σ
    have hz0 : ((z : ↥F) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      apply z.ne_zero
      exact Subtype.ext h0
    have hε : (kummerRoot p F x / ((z : ↥F) : AlgebraicClosure ℚ)) ^ p = 1 := by
      rw [div_pow, kummerRoot_pow, ← hz, div_eq_one_iff_eq (pow_ne_zero _ hz0)]
      show (((z ^ p : (↥F)ˣ) : ↥F) : AlgebraicClosure ℚ) = ((z : ↥F) : AlgebraicClosure ℚ) ^ p
      rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
    have hεF := CycBaseKummer.mem_of_pow_eq_one p ζ hζ F hζF hε
    have hyF : kummerRoot p F x ∈ F := by
      have : kummerRoot p F x = kummerRoot p F x / ((z : ↥F) : AlgebraicClosure ℚ) * ((z : ↥F) : AlgebraicClosure ℚ) :=
        (div_mul_cancel₀ _ hz0).symm
      rw [this]
      exact mul_mem hεF (z : ↥F).2
    exact CycBaseKummer.apply_eq_of_mem F σ.2 hyF

end S_NumberField_LevelArith_kummerChar_eq_zero_iff
end P2MW
export P2MW.S_NumberField_LevelArith_kummerChar_eq_zero_iff (solution)
