-- Prove2me | solution 1 for GroundTheory.Global.one_le_dedekindZetaReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:29.860408+00:00
-- url     : https://prove2.me/submissions/dc19eb2f-6c84-42ae-9620-8cf8d643a4f3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_sum_rpow_neg_le_dedekindZetaReal

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
namespace GroundTheory.Global
theorem _root_.solution {s : ℝ} (hζ : Summable (dedekindZetaTerm K s)) :
    1 ≤ dedekindZetaReal K s := by
  have := sum_rpow_neg_le_dedekindZetaReal {(⊤ : Ideal (𝓞 K))} hζ
  simpa using this
end GroundTheory.Global
