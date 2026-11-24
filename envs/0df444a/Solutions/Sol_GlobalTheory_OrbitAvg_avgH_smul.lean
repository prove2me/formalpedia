-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.avgH_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:31.258981+00:00
-- url     : https://prove2.me/submissions/b1ea38f0-3c53-434b-9c5a-af641d8b9c8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)
namespace GlobalTheory.OrbitAvg
theorem _root_.solution (H : Subgroup L) [H.FiniteIndex] (c : ℂ) (x : V) :
    avgH π L H (c • x) = c • avgH π L H x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH cv
  simp only [finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum, smul_comm c]
end GlobalTheory.OrbitAvg
