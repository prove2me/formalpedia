-- Prove2me | solution 1 for NumberField.LevelArith.exists_level_comp_eq_of_le_sUnitsMaxRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bf2772de-cae8-5cd9-8fde-b159a4f07cc4

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_level_comp_eq_of_le_sUnitsMaxRep

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem solution
    (S : Finset Nat.Primes) (L F F' : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F] [Normal ℚ ↥F'] (hFF' : F ≤ F')
    (n : ℕ) (f : (Fin n → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
    ∃ f' : (Fin n → (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      ∀ g : Fin n → ↥L.fixingSubgroup,
        ((f' (fun i => (g i : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by
  have hU : F'.fixingSubgroup.comap L.fixingSubgroup.subtype ≤ F.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    groupCohomology.comap_fixingSubgroup_antitone L.fixingSubgroup.subtype hFF'
  let π : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype) →
      (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
    QuotientGroup.map _ _ (MonoidHom.id _) (by simpa using hU)
  refine ⟨fun x => ⟨(f (fun i => π (x i))).1, fun u => (f (fun i => π (x i))).2 ⟨u.1, hU u.2⟩⟩, fun g => rfl⟩

end S_NumberField_LevelArith_exists_level_comp_eq_of_le_sUnitsMaxRep
end P2MW
export P2MW.S_NumberField_LevelArith_exists_level_comp_eq_of_le_sUnitsMaxRep (solution)
