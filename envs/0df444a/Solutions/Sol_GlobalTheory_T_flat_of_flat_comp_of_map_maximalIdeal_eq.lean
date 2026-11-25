-- Prove2me | solution 1 for GlobalTheory.T.flat_of_flat_comp_of_map_maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:09.1709+00:00
-- url     : https://prove2.me/submissions/f4011633-d5b4-45c3-94ec-b0b66c4860a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomFlatOfCompFlatOfMapMaximalIdeal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomFlatOfCompFlatOfMapMaximalIdealStatement
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_ringHom_flat_of_comp_flat_of_map_maximalIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E] (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' → IsLocalHom b → (b.comp φ').Flat → b.Flat := by
  first | exact @GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal | exact GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal | (intros; apply GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal <;> assumption)
end _root_.GlobalTheory.T
