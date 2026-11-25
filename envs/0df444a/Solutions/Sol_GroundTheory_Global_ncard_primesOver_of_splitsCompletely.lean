-- Prove2me | solution 1 for GroundTheory.Global.ncard_primesOver_of_splitsCompletely
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:36.90885+00:00
-- url     : https://prove2.me/submissions/cdd65b35-41a8-4226-ae2d-169e96ac5236

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_ncard_primesOver

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
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)}
    (hv : SplitsCompletely L v) : (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L :=
  (splitsCompletely_iff_ncard_primesOver L v).mp hv
end GroundTheory.Global
