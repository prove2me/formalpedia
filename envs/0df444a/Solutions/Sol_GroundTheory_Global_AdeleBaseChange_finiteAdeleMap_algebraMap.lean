-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:35.391928+00:00
-- url     : https://prove2.me/submissions/ffde62e9-21ce-48ca-bf6c-77ed6adf3b3e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (k : K) :
    finiteAdeleMap K L (algebraMap K _ k) = algebraMap L _ (algebraMap K L k) := by
  refine FiniteAdeleRing.ext (K := L) fun w ↦ ?_
  exact (completionMap_algebraMap (below K w) w k).trans
    (IsScalarTower.algebraMap_apply K L (w.adicCompletion L) k)
end GroundTheory.Global.AdeleBaseChange
