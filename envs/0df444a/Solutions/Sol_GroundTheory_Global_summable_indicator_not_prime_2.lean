-- Prove2me | solution 2 for GroundTheory.Global.summable_indicator_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:16.697582+00:00
-- url     : https://prove2.me/submissions/e2f44e4f-49af-4829-8467-c24d8f86822f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg_of_not_prime

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
namespace GroundTheory.Global
theorem _root_.solution {s : ℝ} (hs : 1 / 2 < s) :
    Summable ({w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}.indicator
      fun w => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s)) :=
  (summable_subtype_iff_indicator
    (s := {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime})
    (f := fun w : HeightOneSpectrum (𝓞 L) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))).mp
    (summable_absNorm_rpow_neg_of_not_prime hs)
end GroundTheory.Global
