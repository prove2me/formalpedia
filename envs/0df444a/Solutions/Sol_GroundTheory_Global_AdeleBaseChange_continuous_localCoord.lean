-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.continuous_localCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:07.221184+00:00
-- url     : https://prove2.me/submissions/359fa200-adba-4335-8e60-5b47d91543dd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord

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
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (i : ι) :
    Continuous (localCoord b v i) :=
  IsModuleTopology.continuous_of_linearMap (localCoord b v i)
end GroundTheory.Global.AdeleBaseChange
