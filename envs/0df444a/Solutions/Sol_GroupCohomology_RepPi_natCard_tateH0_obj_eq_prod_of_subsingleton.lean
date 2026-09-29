-- Prove2me | solution 1 for GroupCohomology.RepPi.natCard_tateH0_obj_eq_prod_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/80d6904b-c1f3-5c31-8d15-de5acea7961e

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi
import Theorems.Thm_GroupCohomology_RepPi_nonempty_tateH0_obj_linearEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) (s : Finset ι) (h : ∀ i, i ∉ s → Subsingleton (F i).tateH0) :
    Nat.card (GroupCohomology.RepPi.obj F).tateH0 = ∏ i ∈ s, Nat.card (F i).tateH0 := by
  classical
  obtain ⟨e⟩ := GroupCohomology.RepPi.nonempty_tateH0_obj_linearEquiv F
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun i => (F i).tateH0)),
    Nat.card_prod, Nat.card_pi, Finset.prod_coe_sort s (fun i => Nat.card (F i).tateH0)]
  haveI : ∀ i : {i // ¬ i ∈ s}, Subsingleton (F i).tateH0 := fun i => h i.1 i.2
  rw [Nat.card_of_subsingleton (0 : (i : {i // ¬ i ∈ s}) → (F i).tateH0), mul_one]

end S_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton
end P2MW
export P2MW.S_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton (solution)
