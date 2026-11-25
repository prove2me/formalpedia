-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.cyclicHerbrand_unitsRep_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:55.445792+00:00
-- url     : https://prove2.me/submissions/6e913514-4b3a-4d0b-bef7-d0f53cefafd6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Theorems.Thm_GroundTheory_Global_InfinitePlace_natCard_kerModRange_cycSub_normHom
import Theorems.Thm_GroundTheory_Global_InfinitePlace_natCard_kerModRange_normHom_cycSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
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
variable {v w}
variable (v w)
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (hv : v.IsReal) (hw : w.IsComplex) :
    cyclicHerbrand (unitsRep v w) (completionConj hv) = 2 := by
  rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_cycSub_normHom v w hv hw,
    natCard_kerModRange_normHom_cycSub v w hv hw]
  norm_num
end GroundTheory.Global.InfinitePlace
