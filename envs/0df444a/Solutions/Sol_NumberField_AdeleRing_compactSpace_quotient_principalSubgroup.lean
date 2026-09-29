-- Prove2me | solution 1 for NumberField.AdeleRing.compactSpace_quotient_principalSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b407537c-7401-519f-b8c3-67525703df21

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup

set_option Elab.async false
set_option autoImplicit false

open NumberField NumberField.AdelicBox

theorem solution (F : Type) [Field F] [NumberField F] :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  rw [← isCompact_univ_iff]

  have hcont : Continuous
      (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) :=
    continuous_quot_mk
  have hsurj : (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) '' C
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y

    obtain ⟨x, rfl⟩ := Quot.exists_rep y
    obtain ⟨k, hk, -⟩ := existsUnique_algebraMap_add_mem_adelicBox F x
    refine ⟨algebraMap F (AdeleRing (𝓞 F) F) k + x, hsub hk, ?_⟩

    refine (QuotientAddGroup.eq (s := AdeleRing.principalSubgroup (𝓞 F) F)).mpr ?_
    refine ⟨-k, ?_⟩
    simp only [map_neg]
    abel
  rw [← hsurj]
  exact hC.image hcont

end S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup
end P2MW
export P2MW.S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup (solution)
