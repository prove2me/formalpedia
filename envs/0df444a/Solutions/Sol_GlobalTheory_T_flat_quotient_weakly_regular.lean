-- Prove2me | solution 1 for GlobalTheory.T.flat_quotient_weakly_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:09.577163+00:00
-- url     : https://prove2.me/submissions/03342e64-9926-4bea-a54c-4fa009bc3a61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegularStatement
import Theorems.Thm_GlobalTheory_flat_quotient_ofList_of_isWeaklyRegular_closedFibre


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by
  first | exact @GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre | exact GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre | (intros; apply GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre <;> assumption)
end _root_.GlobalTheory.T
