-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.adeleMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:36.697484+00:00
-- url     : https://prove2.me/submissions/21bc9d9e-ffb0-4eba-8b3e-bd735e20186d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_algebraMap
import Theorems.Thm_GroundTheory_Global_InfinitePlace_infiniteAdeleRingMap_algebraMap


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
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (k : K) :
    adeleMap K L (algebraMap K 𝔸[K] k) = algebraMap L 𝔸[L] (algebraMap K L k) :=
  Prod.ext (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap k)
    (finiteAdeleMap_algebraMap k)
end GroundTheory.Global.AdeleBaseChange
