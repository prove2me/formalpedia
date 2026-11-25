-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.continuous_adeleMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:05:39.181361+00:00
-- url     : https://prove2.me/submissions/91062f49-75b7-44f3-8e17-f457470763de

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_finiteAdeleMap
import Theorems.Thm_GroundTheory_Global_InfinitePlace_continuous_infiniteAdeleRingMap


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
theorem _root_.solution : Continuous (adeleMap K L) :=
  GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap.prodMap continuous_finiteAdeleMap
end GroundTheory.Global.AdeleBaseChange
