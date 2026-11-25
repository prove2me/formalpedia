-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.adeleBasis_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:47.519846+00:00
-- url     : https://prove2.me/submissions/0e2f02d6-5894-4cf9-b270-0d0270240c12

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_sum_coord
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_tmul
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_algebraMap_adeleRing


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
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (y : 𝔸[L]) (i : ι) : (adeleBasis b).repr y i = coord b i y := by
  have hy : ∑ j, coord b j y • adeleBasis b j = y := by
    conv_rhs => rw [← adeleTensorEquiv_sum_coord b y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [adeleTensorEquiv_tmul, adeleBasis_apply, Algebra.smul_def, algebraMap_adeleRing, mul_comm]
  conv_lhs => rw [← hy]
  rw [Basis.repr_sum_self]
end GroundTheory.Global.AdeleBaseChange
