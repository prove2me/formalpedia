-- Prove2me | solution 1 for GlobalTheory.DualFormExists.riemannClL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:56.52921+00:00
-- url     : https://prove2.me/submissions/88a06e41-5d94-4786-a959-8cb18c7916f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualFormExistsUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
noncomputable section
open GlobalTheory GlobalTheory.DualFormExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.DualFormExists
theorem _root_.solution (ξ x : E) : riemannClL ξ x = riemannCl ξ x := rfl
end GlobalTheory.DualFormExists
