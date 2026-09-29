-- Prove2me | solution 1 for NumberField.LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1020ca69-0090-5eac-8d2c-81292e5985a3

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
import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import Theorems.Thm_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois NumberField.LevelArith.instCommGroupUnitsModPow"
p2m_attr_erase "simp" "groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem solution
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S) :
    ∃ (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
      (_ : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
      (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
        NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)),
      Function.Bijective φ.hom ∧
      ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
  haveI : Normal ↥L ↥(levelField L F hLF) := IsGalois.to_normal
  obtain ⟨hsurj, hker⟩ := NumberField.LevelArith.levelGal_surjective_and_ker L F hLF
  obtain ⟨e, hval, hequiv⟩ :=
    NumberField.LevelArith.exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep S L F hLF hF

  let ι : LevelGal L F hLF →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
    (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom.comp
      (QuotientGroup.quotientKerEquivOfSurjective (levelGal L F hLF) hsurj).symm.toMonoidHom
  have hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) =
      (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) := fun g => by
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective (levelGal L F hLF) hsurj).symm (levelGal L F hLF g) =
        (g : ↥L.fixingSubgroup ⧸ (levelGal L F hLF).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.quotientMulEquivOfEq hker
      ((QuotientGroup.quotientKerEquivOfSurjective (levelGal L F hLF) hsurj).symm (levelGal L F hLF g)) = _
    rw [h1, QuotientGroup.quotientMulEquivOfEq_mk]

  have hequiv' : ∀ (q : LevelGal L F hLF) (x),
      e ((((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)).ρ (ι q)) x) =
        (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ q (e x) := by
    intro q x
    obtain ⟨g, rfl⟩ := hsurj q
    rw [hι]
    exact hequiv g x

  let φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) :=
    Rep.ofHom ⟨e.toAddMonoidHom.toIntLinearMap, fun q => LinearMap.ext fun x => hequiv' q x⟩
  refine ⟨ι, hι, φ, e.bijective, fun x => hval x⟩

end S_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
end P2MW
export P2MW.S_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective (solution)
