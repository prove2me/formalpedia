-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.cycSub_unitsRep_toMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:03.694019+00:00
-- url     : https://prove2.me/submissions/11c38051-06de-4023-9c80-23ec0aabc6b7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Theorems.Thm_GroundTheory_Global_InfinitePlace_unitsRep_toMul
import Theorems.Thm_GroundTheory_Global_cycSub_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.cycSub_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.ProfCoh
  GroundTheory.GroupCoh
open scoped NumberField.LiesOver ComplexConjugate
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]
variable (v)
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (σ : Gal(w.Completion/v.Completion)) (x : Additive w.Completionˣ) :
    ((cycSub (unitsRep v w) σ x).toMul : w.Completion) =
      σ (x.toMul : w.Completion) / (x.toMul : w.Completion) := by
  rw [cycSub_apply, toMul_sub, Units.val_div_eq_div_val, unitsRep_toMul]
end GroundTheory.Global.InfinitePlace
