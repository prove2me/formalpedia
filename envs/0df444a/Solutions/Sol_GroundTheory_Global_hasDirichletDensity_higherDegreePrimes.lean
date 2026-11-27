-- Prove2me | solution 1 for GroundTheory.Global.hasDirichletDensity_higherDegreePrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:46.190705+00:00
-- url     : https://prove2.me/submissions/f842c14f-17c1-4c4e-b38e-515f5ebf20c3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_hasDirichletDensity_zero_of_isBoundedUnder
import Theorems.Thm_GroundTheory_Global_isBoundedUnder_primeIdealZetaSum_higherDegreePrimes


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
theorem _root_.solution :
    (higherDegreePrimes K L).HasDirichletDensity 0 :=
  hasDirichletDensity_zero_of_isBoundedUnder
    (isBoundedUnder_primeIdealZetaSum_higherDegreePrimes K L)
end GroundTheory.Global
