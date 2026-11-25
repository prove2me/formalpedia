-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_sum_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:20:07.267213+00:00
-- url     : https://prove2.me/submissions/4f386232-0662-4314-82a5-8a53cf3920c6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_tmul
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (y : 𝔸[L]) :
    adeleTensorEquiv K L (∑ i, b i ⊗ₜ coord b i y) = y := by
  rw [map_sum]
  simp_rw [adeleTensorEquiv_tmul]
  refine Prod.ext ?_ ?_
  · change fstAddHom (∑ i, algebraMap L 𝔸[L] (b i) * adeleMap K L (coord b i y)) = y.1
    rw [map_sum]
    conv_rhs => rw [← GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y.1]
    rw [map_sum]
    simp_rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul']
    rfl
  · change sndAddHom (∑ i, algebraMap L 𝔸[L] (b i) * adeleMap K L (coord b i y)) = y.2
    rw [map_sum]
    conv_rhs => rw [← finiteTensorMap_sum_finiteCoord b y.2]
    rw [map_sum]
    simp_rw [finiteTensorMap_tmul]
    rfl
end GroundTheory.Global.AdeleBaseChange
