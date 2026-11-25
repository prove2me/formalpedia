-- Prove2me | solution 1 for GlobalTheory.T.endomorphismFamily_direct_summand_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:42.931119+00:00
-- url     : https://prove2.me/submissions/312237af-6457-4549-ab7a-ed20abacfe22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismFamilyDirectSummandCancellation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismFamilyDirectSummandCancellationStatement
import Theorems.Thm_GlobalTheory_endFamily_cancel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V'] [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V) (b : ι → Module.End k V') (c : ι → Module.End k U), (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) → ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  first | exact @GlobalTheory.endFamily_cancel | exact GlobalTheory.endFamily_cancel | (intros; apply GlobalTheory.endFamily_cancel <;> assumption)
end _root_.GlobalTheory.T
