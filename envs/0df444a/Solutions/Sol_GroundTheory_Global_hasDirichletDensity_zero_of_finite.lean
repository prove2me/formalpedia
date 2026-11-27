-- Prove2me | solution 1 for GroundTheory.Global.hasDirichletDensity_zero_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:54.311797+00:00
-- url     : https://prove2.me/submissions/a0f4146e-5532-4dd5-aa60-df2d4ae29d2c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_hasDirichletDensity_zero_of_isBoundedUnder
import Theorems.Thm_GroundTheory_Global_isBoundedUnder_primeIdealZetaSum_of_finite

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
    (hS : S.Finite) : S.HasDirichletDensity 0 :=
  hasDirichletDensity_zero_of_isBoundedUnder (isBoundedUnder_primeIdealZetaSum_of_finite hS)
end GroundTheory.Global
