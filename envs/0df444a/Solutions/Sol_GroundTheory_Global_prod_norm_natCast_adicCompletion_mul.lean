-- Prove2me | solution 1 for GroundTheory.Global.prod_norm_natCast_adicCompletion_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:27.860132+00:00
-- url     : https://prove2.me/submissions/7d2cb1ed-f31a-4802-b734-a045ee11ccaf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Theorems.Thm_GroundTheory_Global_norm_natCast_adicCompletion_eq_one
import Theorems.Thm_GroundTheory_Global_finprod_norm_natCast_adicCompletion_mul

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
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) * (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  rw [← finprod_eq_prod_of_mulSupport_subset]
  · exact finprod_norm_natCast_adicCompletion_mul hn
  · intro v hv
    by_contra h
    exact hv (norm_natCast_adicCompletion_eq_one fun h' ↦ h (hS v h'))
end GroundTheory.Global
