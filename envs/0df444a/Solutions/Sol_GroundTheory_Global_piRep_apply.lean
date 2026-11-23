-- Prove2me | solution 1 for GroundTheory.Global.piRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:47.024315+00:00
-- url     : https://prove2.me/submissions/295b9079-9056-4931-b750-a9db00aaaaad

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G ι : Type*} [CommRing k] [Group G] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)]
namespace GroundTheory.Global
theorem _root_.solution (ρ : ∀ i, Representation k G (V i)) (g : G) (x : ∀ i, V i) (i : ι) :
    piRep ρ g x i = ρ i g (x i) :=
  rfl
end GroundTheory.Global
