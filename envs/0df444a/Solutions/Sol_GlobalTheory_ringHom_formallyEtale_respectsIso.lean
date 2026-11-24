-- Prove2me | solution 1 for GlobalTheory.ringHom_formallyEtale_respectsIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:58.92967+00:00
-- url     : https://prove2.me/submissions/e90052e1-90dd-4ad3-a867-0349cc153848

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
import Theorems.Thm_GlobalTheory_ringHom_formallyEtale_of_ringEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution : RingHom.RespectsIso.{u} @RingHom.FormallyEtale := by
  have hiso := @ringHom_formallyEtale_of_ringEquiv.{u}
  constructor
  · intro R S T _ _ _ f e hf
    exact RingHom.FormallyEtale.comp hf (hiso e)
  · intro R S T _ _ _ f e hf
    exact RingHom.FormallyEtale.comp (hiso e) hf
end GlobalTheory
