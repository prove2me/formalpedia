-- Prove2me | solution 1 for GroundTheory.Global.prod_norm_natCast_mul_prod_infinitePlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:30.441832+00:00
-- url     : https://prove2.me/submissions/656b0b1d-80ed-4315-8b82-049f58252961

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Theorems.Thm_GroundTheory_Global_prod_norm_natCast_adicCompletion_mul
import Theorems.Thm_GroundTheory_Global_prod_norm_natCast_infinitePlaceCompletion_pow_mult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ} (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) *
      ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = 1 := by
  rw [prod_norm_natCast_infinitePlaceCompletion_pow_mult]
  exact prod_norm_natCast_adicCompletion_mul hn S hS
end GroundTheory.Global
