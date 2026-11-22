-- Prove2me | solution 1 for Log.CompatibleComputations.compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:16:59.117824+00:00
-- url     : https://prove2.me/submissions/3609c318-3b9f-45e3-bcfc-890039ddc087

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R
namespace Log
namespace CompatibleComputations
theorem _root_.solution {l : Set F.Event}
    (σ : CompatibleComputations F R l) : CompatibleComputations.val F R σ ⊨ l := σ.2
end CompatibleComputations
end Log
