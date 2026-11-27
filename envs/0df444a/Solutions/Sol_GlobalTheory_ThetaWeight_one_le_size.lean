-- Prove2me | solution 1 for GlobalTheory.ThetaWeight.one_le_size
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:05.27875+00:00
-- url     : https://prove2.me/submissions/35d6e4f5-8639-4aa1-9147-d1044e56f0ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaWeightData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ThetaWeight
open Finset
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.ThetaWeight
theorem _root_.solution {m : ℤ} (hm : 0 ≤ m) {G : (ι → ℤ) × ℤ} (hG : 0 ≤ G.2) : 1 ≤ size m G := by
  have h1 : 0 ≤ ∑ i, |G.1 i| := sum_nonneg fun i _ => abs_nonneg _
  have h2 := mul_nonneg hm hG
  unfold size
  linarith
end GlobalTheory.ThetaWeight
