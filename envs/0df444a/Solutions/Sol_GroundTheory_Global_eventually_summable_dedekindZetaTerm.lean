-- Prove2me | solution 1 for GroundTheory.Global.eventually_summable_dedekindZetaTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:44.274645+00:00
-- url     : https://prove2.me/submissions/285e1302-e6de-4017-affb-cbd406bf2765

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_tendsto_sub_one_mul_dedekindZetaReal

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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace GroundTheory.Global
theorem _root_.solution :
    ∀ᶠ s in 𝓝[>] (1 : ℝ), Summable (dedekindZetaTerm K s) := by
  have h := (tendsto_sub_one_mul_dedekindZetaReal K).eventually
    (lt_mem_nhds (dedekindZeta_residue_pos K))
  filter_upwards [h] with s hs
  by_contra hns
  rw [dedekindZetaReal, tsum_eq_zero_of_not_summable hns, mul_zero] at hs
  exact lt_irrefl _ hs
end GroundTheory.Global
