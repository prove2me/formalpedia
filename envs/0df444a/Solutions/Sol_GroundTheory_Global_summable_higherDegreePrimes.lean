-- Prove2me | solution 1 for GroundTheory.Global.summable_higherDegreePrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:08.313575+00:00
-- url     : https://prove2.me/submissions/f237c317-9ac4-4c3a-8d4c-dbd28948c2e3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_higherDegreePrimes_subset
import Theorems.Thm_GroundTheory_Global_summable_indicator_not_prime

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
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]
variable (K L) [Field K] [NumberField K] [Algebra K L]
variable {K L}
variable (K L)
namespace GroundTheory.Global
theorem _root_.solution {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun w : higherDegreePrimes K L => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := by
  refine (summable_subtype_iff_indicator (s := higherDegreePrimes K L)
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mpr ?_
  refine Summable.of_nonneg_of_le (fun w => indicator_nonneg (fun _ _ => by positivity) w)
    (fun w => ?_) (summable_indicator_not_prime hs)
  exact indicator_le_indicator_of_subset higherDegreePrimes_subset (fun _ => by positivity) w
end GroundTheory.Global
