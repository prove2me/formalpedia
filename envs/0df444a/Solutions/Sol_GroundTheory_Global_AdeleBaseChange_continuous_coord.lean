-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.continuous_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:10:26.787203+00:00
-- url     : https://prove2.me/submissions/3f515a15-33de-4440-9d68-acc99b300696

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_finiteCoord


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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (i : ι) : Continuous (coord b i) :=
  ((GroundTheory.Global.InfinitePlace.continuous_adeleCoord b i).comp continuous_fst).prodMk
    ((continuous_finiteCoord b i).comp continuous_snd)
end GroundTheory.Global.AdeleBaseChange
