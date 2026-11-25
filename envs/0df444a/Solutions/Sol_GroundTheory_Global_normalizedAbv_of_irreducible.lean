-- Prove2me | solution 1 for GroundTheory.Global.normalizedAbv_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:57.064606+00:00
-- url     : https://prove2.me/submissions/8571412c-1d2f-4a65-a343-feaa626137e7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Theorems.Thm_GroundTheory_Global_valued_of_irreducible
import Theorems.Thm_GroundTheory_Global_normalizedAbv_eq_zpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    normalizedAbv v (ϖ : v.adicCompletion K) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have h0 : (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  rw [normalizedAbv_eq_zpow v h0, valued_of_irreducible v hϖ, log_exp, zpow_neg_one]
end GroundTheory.Global
