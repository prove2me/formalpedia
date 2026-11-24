-- Prove2me | solution 1 for GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:39:27.071833+00:00
-- url     : https://prove2.me/submissions/17561fe7-7cfc-4da4-9575-c98c7233d1fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsNoetherianRingOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Theorems.Thm_GlobalTheory_AdicNoeth_isNoetherianRing_of_isAdicComplete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicNoeth
namespace GlobalTheory.AdicNoeth
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsNoetherianRing (AdicCompletion I R) := by
  intro R _ _ I
  have fg : I.FG := I.fg_of_isNoetherianRing
  have hc := AdicCompletion.isAdicComplete_self I fg
  have e : (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) ≃+* R ⧸ I := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I)
  exact isNoetherianRing_of_isAdicComplete _ _ (fg.map _) hc
    (isNoetherianRing_of_ringEquiv _ e.symm)
end GlobalTheory.AdicNoeth
