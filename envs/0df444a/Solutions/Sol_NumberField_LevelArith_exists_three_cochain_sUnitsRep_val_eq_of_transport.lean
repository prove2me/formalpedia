-- Prove2me | solution 1 for NumberField.LevelArith.exists_three_cochain_sUnitsRep_val_eq_of_transport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bfbaac44-769c-50a0-afdb-d4f75dea7979

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
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_three_cochain_sUnitsRep_val_eq_of_transport

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem solution
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)]
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφ : Function.Bijective φ.hom)
    (hφval : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
    ∃ f₁ : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)),
      (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0 → ((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 3 4).hom f₁ = 0) ∧
      ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (f₁ (fun i => levelGal L F hLF (g i))) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
  let T := groupCohomology.cochainsMap ι φ
  have hcomm : ∀ (i j : ℕ) x, ((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF)
      (placesOverPrimesFinset ↥L S))).d i j).hom ((T.f i).hom x) =
      (T.f j).hom (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants
        (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d i j).hom x) := fun i j x =>
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (T.comm i j)) x
  refine ⟨(T.f 3).hom f, fun hf => ?_, fun g => ?_⟩
  · rw [hcomm, hf, map_zero]
  · have hg : (fun i => ι (levelGal L F hLF (g i))) =
        fun i => (g i : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) := funext fun i => hι (g i)
    change ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)
      (φ.hom (f (fun i => ι (levelGal L F hLF (g i))))) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = _
    rw [hg]
    exact hφval _

end S_NumberField_LevelArith_exists_three_cochain_sUnitsRep_val_eq_of_transport
end P2MW
export P2MW.S_NumberField_LevelArith_exists_three_cochain_sUnitsRep_val_eq_of_transport (solution)
