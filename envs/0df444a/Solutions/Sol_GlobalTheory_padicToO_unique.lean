-- Prove2me | solution 1 for GlobalTheory.padicToO_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:30.730246+00:00
-- url     : https://prove2.me/submissions/15a8629d-b88c-4924-95d2-d6d4e37a7d1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicRingHomEqCanonical
import Theorems.Thm_GlobalTheory_padicInt_ringHom_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (g : ℤ_[p] →+* O), g = padicToO p O := by
  intro p _ O _ _ _ g
  exact padicInt_ringHom_ext p O g (padicToO p O)
end GlobalTheory
