-- Prove2me | solution 1 for NumberField.LevelArith.sUnitsMaxRep_smooth_and_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/259b681b-182a-55f3-9938-a222ac7e745d

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Theorems.Thm_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_sUnitsMaxRep_smooth_and_divisible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

open scoped TensorProduct Pointwise

local instance CycBaseDiv.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    (∀ a : sUnitsMaxRep S L, IsLevelConstantSr₁ L.fixingSubgroup.subtype S (fun g : ↥L.fixingSubgroup => (sUnitsMaxRep S L).ρ g a)) ∧
      ∀ x : sUnitsMaxRep S L, ∃ y : sUnitsMaxRep S L, (p : ℤ) • y = x := by
  have hp : p.Prime := Fact.out
  constructor
  ·
    intro a
    obtain ⟨⟨F, hF, haF⟩, -⟩ := sUnitsMaxStable_le S L (a.2 : sUnitsMaxRep.val S L a ∈ sUnitsMaxStable S L)
    refine ⟨F, hF, fun g s hs => ?_⟩
    have hfix : (sUnitsMaxRep S L).ρ s a = a := by
      apply Subtype.ext
      show Additive.ofMul ((s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • sUnitsMaxRep.val S L a) = a.1
      apply congrArg Additive.ofMul
      apply Units.ext
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs _ haF
    show (sUnitsMaxRep S L).ρ (g * s) a = (sUnitsMaxRep S L).ρ g a
    rw [map_mul, Module.End.mul_apply, hfix]
  ·
    intro x
    have hu : sUnitsMaxRep.val S L x ∈ sUnitsMax S := sUnitsMaxStable_le S L x.2
    obtain ⟨⟨F, hF, huF⟩, hunit⟩ := hu
    obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_pow_nat_eq ((sUnitsMaxRep.val S L x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) hp.pos
    have hu0 : ((sUnitsMaxRep.val S L x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ≠ 0 := Units.ne_zero _
    have hy0 : y₀ ≠ 0 := fun h => hu0 (by rw [← hy₀, h, zero_pow hp.ne_zero])

    have hunit' : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
        ((sUnitsMaxRep.val S L x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧
          (((sUnitsMaxRep.val S L x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))⁻¹ ∈ A := by
      intro q hq A hA
      obtain ⟨h1, h2⟩ := hunit q hq A hA
      rw [Units.val_inv_eq_inv_val] at h2
      exact ⟨h1, h2⟩

    have hlev : (F ⊔ IntermediateField.adjoin ℚ {y₀}).IsUnramifiedOutside S :=
      IntermediateField.isUnramifiedOutside_sup_adjoin_of_pow_eq S (pPrime p) hpS F hF _ huF hunit' y₀ hy₀

    have hyunit : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
        y₀ ∈ A ∧ y₀⁻¹ ∈ A := by
      intro q hq A hA
      obtain ⟨h1, h2⟩ := hunit' q hq A hA
      have hv : A.valuation ((sUnitsMaxRep.val S L x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = 1 := by
        apply le_antisymm ((A.valuation_le_one_iff _).mpr h1)
        have h := (A.valuation_le_one_iff _).mpr h2
        rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hu0))] at h
        exact h
      have hvy : A.valuation y₀ = 1 := by
        have h := congrArg A.valuation hy₀
        rw [map_pow, hv] at h
        exact (pow_eq_one_iff_left hp.ne_zero).mp h
      refine ⟨(A.valuation_le_one_iff _).mp hvy.le, (A.valuation_le_one_iff _).mp ?_⟩
      rw [map_inv₀, hvy, inv_one]
    have hymem : Units.mk0 y₀ hy0 ∈ sUnitsMaxStable S L := by
      rw [sUnitsMaxStable_eq_sUnitsMax]
      refine ⟨⟨F ⊔ IntermediateField.adjoin ℚ {y₀}, hlev, ?_⟩, fun q hq A hA => ?_⟩
      · exact (le_sup_right : IntermediateField.adjoin ℚ {y₀} ≤ _) (IntermediateField.mem_adjoin_simple_self ℚ y₀)
      · obtain ⟨h1, h2⟩ := hyunit q hq A hA
        refine ⟨h1, ?_⟩
        rw [Units.val_inv_eq_inv_val, Units.val_mk0]
        exact h2
    refine ⟨⟨Additive.ofMul (Units.mk0 y₀ hy0), hymem⟩, ?_⟩
    apply Subtype.ext
    show ((p : ℤ) • Additive.ofMul (Units.mk0 y₀ hy0) : Additive (AlgebraicClosure ℚ)ˣ) = x.1
    rw [← ofMul_zpow, zpow_natCast,
      show Units.mk0 y₀ hy0 ^ p = sUnitsMaxRep.val S L x from Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hy₀)]
    rfl

end S_NumberField_LevelArith_sUnitsMaxRep_smooth_and_divisible
end P2MW
export P2MW.S_NumberField_LevelArith_sUnitsMaxRep_smooth_and_divisible (solution)
