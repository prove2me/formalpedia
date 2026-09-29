-- Prove2me | solution 1 for M4aHerbrand.map_prInf_eq_zero_of_pow_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/16090785-329a-5ad0-9134-3d41a9d05aaf

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_map_prInf_eq_zero_of_pow_smul_eq_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]

    (prInf : ∀ v : InfinitePlace F,
      Rep.res (NumberField.InfPlaceDecomp.decomp E F v).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ NumberField.InfPlaceDecomp.localUnits E F v)
    (p : ℕ) [Fact p.Prime]
    (hinf2 : p = 2 → ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2) (k : ℕ) (hxk : (p ^ k : ℤ) • x = 0)
    (v : InfinitePlace F) :
    (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F v).subtype (prInf v) 2).hom x = 0 := by

  set z := (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F v).subtype (prInf v) 2).hom x with hz
  have hpz : (p ^ k : ℤ) • z = 0 := by rw [hz, ← map_zsmul, hxk, map_zero]
  have hcard : Nat.card ↥(NumberField.InfPlaceDecomp.decomp E F v) • z = 0 := by
    obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul (⊥ : Subgroup ↥(NumberField.InfPlaceDecomp.decomp E F v))
      (NumberField.InfPlaceDecomp.localUnits E F v) 2
    haveI := ModuleCat.subsingleton_of_isZero (isZero_groupCohomology_succ_of_subsingleton
      (Rep.res (⊥ : Subgroup ↥(NumberField.InfPlaceDecomp.decomp E F v)).subtype (NumberField.InfPlaceDecomp.localUnits E F v)) 1)
    have h0 : (groupCohomology.map (⊥ : Subgroup ↥(NumberField.InfPlaceDecomp.decomp E F v)).subtype
        (𝟙 (Rep.res (⊥ : Subgroup ↥(NumberField.InfPlaceDecomp.decomp E F v)).subtype (NumberField.InfPlaceDecomp.localUnits E F v))) 2).hom z = 0 :=
      Subsingleton.elim _ _
    rw [← Subgroup.index_bot, ← hcor z, h0, map_zero]
  rcases NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two E v with h1 | h2
  · have h1' : Nat.card ↥(NumberField.InfPlaceDecomp.decomp E F v) = 1 := h1
    rwa [h1', one_smul] at hcard
  · by_cases hp : p = 2
    ·
      exfalso
      have hsub : Subsingleton ↥(NumberField.InfPlaceDecomp.decomp E F v) :=
        ⟨fun a b => Subtype.ext ((hinf2 hp v a.1 a.2).trans (hinf2 hp v b.1 b.2).symm)⟩
      have : Nat.card ↥(NumberField.InfPlaceDecomp.decomp E F v) = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
      have h2' : Nat.card ↥(NumberField.InfPlaceDecomp.decomp E F v) = 2 := h2
      omega
    ·
      have h2' : Nat.card ↥(NumberField.InfPlaceDecomp.decomp E F v) = 2 := h2
      rw [h2'] at hcard
      have hcop : IsCoprime (2 : ℤ) ((p : ℤ) ^ k) := by
        have : Nat.Coprime 2 (p ^ k) := Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp))
        exact_mod_cast (Nat.isCoprime_iff_coprime.2 this)
      obtain ⟨a, b, hab⟩ := hcop
      have h2z : (2 : ℤ) • z = 0 := by rw [← natCast_zsmul] at hcard; exact_mod_cast hcard
      calc z = (1 : ℤ) • z := (one_zsmul z).symm
        _ = (a * 2 + b * (p : ℤ) ^ k) • z := by rw [hab]
        _ = 0 := by rw [add_zsmul, mul_zsmul, mul_zsmul, h2z, hpz, zsmul_zero, zsmul_zero, add_zero]

end S_M4aHerbrand_map_prInf_eq_zero_of_pow_smul_eq_zero
end P2MW
export P2MW.S_M4aHerbrand_map_prInf_eq_zero_of_pow_smul_eq_zero (solution)
