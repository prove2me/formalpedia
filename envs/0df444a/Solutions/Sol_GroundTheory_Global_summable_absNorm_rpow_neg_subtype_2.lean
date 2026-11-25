-- Prove2me | solution 2 for GroundTheory.Global.summable_absNorm_rpow_neg_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:56.000992+00:00
-- url     : https://prove2.me/submissions/91c94efb-f5ad-4be5-922b-3d5190d48dc2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg

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
namespace GroundTheory.Global
theorem _root_.solution (S : Set (HeightOneSpectrum (𝓞 L))) {s : ℝ}
    (hs : 1 < s) : Summable fun w : S => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) :=
  (summable_absNorm_rpow_neg hs).subtype S
end GroundTheory.Global
