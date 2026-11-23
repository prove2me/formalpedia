-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:27.207534+00:00
-- url     : https://prove2.me/submissions/2b21fbf4-b365-434a-8a3b-1bdcfcb14cfe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply

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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : v.adicCompletion K) : finiteAdeleSingle v x w = 1 := by
  classical
  rw [finiteAdeleSingle_apply]
  exact Pi.mulSingle_eq_of_ne h x
end GroundTheory.Global.IdeleGroup
