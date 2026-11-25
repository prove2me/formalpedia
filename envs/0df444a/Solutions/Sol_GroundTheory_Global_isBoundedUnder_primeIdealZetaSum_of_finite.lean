-- Prove2me | solution 1 for GroundTheory.Global.isBoundedUnder_primeIdealZetaSum_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:58:23.593912+00:00
-- url     : https://prove2.me/submissions/a0ed50a8-c57e-4a75-b270-d857c95e9d19

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity

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
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => S.primeIdealZetaSum s :=
  isBoundedUnder_of_eventually_le (a := S.ncard) (eventually_nhdsWithin_of_forall
    fun s (hs : 1 < s) => Set.primeIdealZetaSum_le_card_of_finite hS (by linarith))
end GroundTheory.Global
