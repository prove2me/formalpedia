-- Prove2me | solution 1 for GroupCohomology.RepPi.subsingleton_tateHneg1_obj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b2aa2e7e-727c-5551-a943-f7deec222093

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi
import Theorems.Thm_GroupCohomology_RepPi_nonempty_tateHneg1_obj_linearEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GroupCohomology_RepPi_subsingleton_tateHneg1_obj

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) (h : ∀ i, Subsingleton (F i).tateHneg1) :
    Subsingleton (GroupCohomology.RepPi.obj F).tateHneg1 := by
  obtain ⟨e⟩ := GroupCohomology.RepPi.nonempty_tateHneg1_obj_linearEquiv F
  exact e.toEquiv.subsingleton_congr.2 inferInstance

end S_GroupCohomology_RepPi_subsingleton_tateHneg1_obj
end P2MW
export P2MW.S_GroupCohomology_RepPi_subsingleton_tateHneg1_obj (solution)
