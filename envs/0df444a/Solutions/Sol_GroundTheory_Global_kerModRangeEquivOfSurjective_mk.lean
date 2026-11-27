-- Prove2me | solution 1 for GroundTheory.Global.kerModRangeEquivOfSurjective_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:54.312224+00:00
-- url     : https://prove2.me/submissions/71508d47-467d-4947-856b-c9fab44d5b0d

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
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
namespace GroundTheory.Global
theorem _root_.solution {f g : A →+ A} (φ : f.ker →+ B)
    (hs : Function.Surjective φ) (hk : ∀ a : f.ker, φ a = 0 ↔ (a : A) ∈ g.range) (a : f.ker) :
    kerModRangeEquivOfSurjective φ hs hk (QuotientAddGroup.mk a : KerModRange f g) = φ a :=
  rfl
end GroundTheory.Global
