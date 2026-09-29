-- Prove2me | solution 1 for NumberField.LevelArith.exists_le_le_isPGroup_quotient_not_dvd_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/86b40eb2-7501-5231-94d8-521adba7540f

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_LevelArith_normal_levelField_of_isNormalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_le_le_isPGroup_quotient_not_dvd_finrank

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem solution
    (p : ℕ) [Fact p.Prime] (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] :
    ∃ (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F) (_ : FiniteDimensional ℚ ↥L')
      (_ : IsGalois ↥L' ↥(levelField L' F hL'F)),
      IsPGroup p (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype) ∧ ¬ p ∣ Module.finrank ↥L ↥(levelField L L' hLL') := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

  let U : Subgroup ↥L.fixingSubgroup := F.fixingSubgroup.comap L.fixingSubgroup.subtype
  haveI : U.FiniteIndex := groupCohomology.finiteIndex_comap_fixingSubgroup L.fixingSubgroup.subtype F
  haveI : Finite (↥L.fixingSubgroup ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨P⟩ : Nonempty (Sylow p (↥L.fixingSubgroup ⧸ U)) := Sylow.nonempty

  let H : Subgroup ↥L.fixingSubgroup := (P : Subgroup (↥L.fixingSubgroup ⧸ U)).comap (QuotientGroup.mk' U)
  let H' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := H.map L.fixingSubgroup.subtype
  have hFΓ : F.fixingSubgroup ≤ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hLF
  have hUH : U ≤ H := fun γ hγ => by
    show QuotientGroup.mk' U γ ∈ (P : Subgroup (↥L.fixingSubgroup ⧸ U))
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff γ).2 hγ]
    exact one_mem _
  have hFH' : F.fixingSubgroup ≤ H' := fun σ hσ => ⟨⟨σ, hFΓ hσ⟩, hUH hσ, rfl⟩
  have hH'Γ : H' ≤ L.fixingSubgroup := Subgroup.map_subtype_le H
  have hopen : IsOpen (H' : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isOpen_mono hFH' F.fixingSubgroup_isOpen
  let Hc : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := ⟨H', Subgroup.isClosed_of_isOpen H' hopen⟩

  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField H'
  have hfix : L'.fixingSubgroup = H' := InfiniteGalois.fixingSubgroup_fixedField Hc
  have hLL' : L ≤ L' := (IntermediateField.le_iff_le _ _).2 hH'Γ
  have hL'F : L' ≤ F := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup F]
    exact (IntermediateField.le_iff_le _ _).2 (hfix.symm ▸ hFH')
  haveI : FiniteDimensional ℚ ↥L' := by
    letI : Algebra ↥L' ↥F := RingHom.toAlgebra (IntermediateField.inclusion hL'F)
    exact FiniteDimensional.left ℚ ↥L' ↥F

  have hnorm : IsNormalLevel L' F := fun g _ s hs => by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
    intro x hx
    have hx' : g⁻¹ x ∈ F := (IntermediateField.normal_iff_forall_map_le'.1 (by assumption) g⁻¹) ⟨x, hx, rfl⟩
    have := hs _ hx'
    simp only [AlgEquiv.mul_apply]
    rw [this]
    simp
  haveI : Normal ↥L' ↥(levelField L' F hL'F) := NumberField.LevelArith.normal_levelField_of_isNormalLevel L' F hL'F hnorm
  haveI : IsGalois ↥L' ↥(levelField L' F hL'F) := ⟨⟩
  refine ⟨L', hLL', hL'F, inferInstance, inferInstance, fun q => ?_, ?_⟩
  ·
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ H' := by rw [← hfix]; exact g.2
    obtain ⟨γ, hγ, hγg⟩ := hg
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨QuotientGroup.mk' U γ, hγ⟩
    refine ⟨n, ?_⟩
    have hn' : (QuotientGroup.mk' U γ) ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hn'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    show ((g ^ p ^ n : ↥L'.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup
    have : ((g ^ p ^ n : ↥L'.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) =
        ((γ ^ p ^ n : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, ← hγg]
      rfl
    rw [this]
    exact hn'
  ·
    have h1 : Module.finrank ℚ ↥L = L.fixingSubgroup.index := IntermediateField.finrank_eq_fixingSubgroup_index _ L
    have h2 : Module.finrank ℚ ↥L' = H'.index := by
      rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    have h3 : H'.index = H.index * L.fixingSubgroup.index := by
      rw [Subgroup.index_map, Subgroup.ker_subtype, sup_bot_eq, Subgroup.range_subtype]
    have h4 : H.index = (P : Subgroup (↥L.fixingSubgroup ⧸ U)).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)
    have htower : Module.finrank ℚ ↥L * Module.finrank ↥L ↥(levelField L L' hLL') = Module.finrank ℚ ↥L' := by
      rw [← IntermediateField.relfinrank_eq_finrank_of_le hLL']
      exact IntermediateField.finrank_bot_mul_relfinrank hLL'
    rw [h2, h3, h4, h1, mul_comm] at htower
    have hpos : 0 < L.fixingSubgroup.index := by rw [← h1]; exact Module.finrank_pos
    have hidx : Module.finrank ↥L ↥(levelField L L' hLL') = (P : Subgroup (↥L.fixingSubgroup ⧸ U)).index :=
      Nat.eq_of_mul_eq_mul_right hpos htower
    rw [hidx]
    exact P.not_dvd_index

end S_NumberField_LevelArith_exists_le_le_isPGroup_quotient_not_dvd_finrank
end P2MW
export P2MW.S_NumberField_LevelArith_exists_le_le_isPGroup_quotient_not_dvd_finrank (solution)
