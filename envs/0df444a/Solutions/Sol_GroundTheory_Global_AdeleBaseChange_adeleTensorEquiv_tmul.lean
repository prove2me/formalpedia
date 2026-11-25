-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:05:25.826801+00:00
-- url     : https://prove2.me/submissions/609cb0e9-f037-4228-b3c8-b780a89c3412

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorEquiv_tmul
import Theorems.Thm_P2M_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul__a0cdac9b4d94


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
theorem _root_.solution (l : L) (a : 𝔸[K]) :
    adeleTensorEquiv K L (l ⊗ₜ a) = algebraMap L 𝔸[L] l * adeleMap K L a :=
  Prod.ext (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul' l a.1)
    (finiteTensorEquiv_tmul l a.2)
end GroundTheory.Global.AdeleBaseChange
