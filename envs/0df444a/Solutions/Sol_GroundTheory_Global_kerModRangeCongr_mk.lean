-- Prove2me | solution 1 for GroundTheory.Global.kerModRangeCongr_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:49.843649+00:00
-- url     : https://prove2.me/submissions/e7303a86-800d-4c40-afad-6827d0552361

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
theorem _root_.solution {fA gA : A →+ A} {fB gB : B →+ B} (e : A ≃+ B)
    (hf : ∀ a, e (fA a) = fB (e a)) (hg : ∀ a, e (gA a) = gB (e a)) (a : fA.ker) :
    kerModRangeCongr e hf hg (QuotientAddGroup.mk a : KerModRange fA gA) =
      QuotientAddGroup.mk (kerMap e.toAddMonoidHom hf a) :=
  rfl
end GroundTheory.Global
