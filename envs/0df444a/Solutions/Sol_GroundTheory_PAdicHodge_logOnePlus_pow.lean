-- Prove2me | solution 1 for GroundTheory.PAdicHodge.logOnePlus_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:15.849804+00:00
-- url     : https://prove2.me/submissions/69e331ad-e9aa-45c1-9df0-59abdbd7570a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_X
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_subst
import Theorems.Thm_GroundTheory_PAdicHodge_log_subst_one_add_X_pow_sub_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.seriesEval_X

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {z : B} (hz : z ∈ I) (k : ℕ) (hk : (1 + z) ^ k - 1 ∈ I) :
    logOnePlus I ((1 + z) ^ k - 1) hk = k * logOnePlus I z hz := by
  have hg : constantCoeff ((1 + X) ^ k - 1 : ℚ⟦X⟧) = 0 := by simp
  rw [logOnePlus, seriesEval_subst hz hg hk (by simp), log_subst_one_add_X_pow_sub_one, map_mul,
    map_natCast, logOnePlus]
end GroundTheory.PAdicHodge
