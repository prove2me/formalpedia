-- Prove2me | solution 1 for GlobalTheory.ringHom_faithfullyFlat_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:43.672613+00:00
-- url     : https://prove2.me/submissions/61ce540e-454f-4838-8fec-2392888a6b21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
namespace GlobalTheory
theorem _root_.solution {f : A →+* B} {g : B →+* B'} (hf : f.FaithfullyFlat)
    (hg : g.FaithfullyFlat) : (g.comp f).FaithfullyFlat := by
  algebraize [f, g, g.comp f]
  exact Module.FaithfullyFlat.trans A B B'
end GlobalTheory
