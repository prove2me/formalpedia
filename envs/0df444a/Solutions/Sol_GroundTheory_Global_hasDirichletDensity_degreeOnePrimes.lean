-- Prove2me | solution 1 for GroundTheory.Global.hasDirichletDensity_degreeOnePrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:01.880966+00:00
-- url     : https://prove2.me/submissions/90167f78-ac9c-42ec-951f-1eed96205f81

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_hasDirichletDensity_univ
import Theorems.Thm_GroundTheory_Global_hasDirichletDensity_inter_degreeOnePrimes_iff

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
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K L)
namespace GroundTheory.Global
theorem _root_.solution : (degreeOnePrimes K L).HasDirichletDensity 1 := by
  have := (hasDirichletDensity_inter_degreeOnePrimes_iff K univ 1).mpr
    (hasDirichletDensity_univ (K := L))
  rwa [univ_inter] at this
end GroundTheory.Global
