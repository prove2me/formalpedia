-- Prove2me | solution 1 for NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_fixedField_sylow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/71c06049-6d46-5e06-b78f-236d1067f952

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_sylow
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (F ≃ₐ[E] F))
    (hinf2 : p = 2 → ∀ (v : InfinitePlace F) (g : F ≃ₐ[E] F), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)
    (v : InfinitePlace F) (g : (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F)) (hg : g ∈ NumberField.InfPlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v) : g = 1 := by
  classical

  have h12 := NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two (↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))) v
  have hcardK : Nat.card (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) = Nat.card (P : Subgroup (F ≃ₐ[E] F)) := by
    rw [← Nat.card_congr (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))).toEquiv, IntermediateField.fixingSubgroup_fixedField]
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  rcases h12 with h1 | h2
  ·
    have hbot : MulAction.stabilizer (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) v = ⊥ := Subgroup.card_eq_one.1 h1
    have : g ∈ (⊥ : Subgroup (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F)) := by rw [← hbot]; exact hg
    exact Subgroup.mem_bot.1 this
  ·
    have hdvd : 2 ∣ Nat.card (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) := h2 ▸ Subgroup.card_subgroup_dvd_card _
    rw [hcardK, hm] at hdvd
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out)).1 (Nat.prime_two.dvd_of_dvd_pow hdvd)).symm
    have hg' : AlgEquiv.restrictScalars E g ∈ NumberField.InfPlaceDecomp.decomp E F v := by
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      exact hg
    have h1 := hinf2 hp2 v (AlgEquiv.restrictScalars E g) hg'
    apply AlgEquiv.ext
    intro x
    exact AlgEquiv.congr_fun h1 x

end S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_sylow
end P2MW
export P2MW.S_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_sylow (solution)
