-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.hasCyclicHerbrand_unitsRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:08.901099+00:00
-- url     : https://prove2.me/submissions/f6ad5739-6b50-4620-b33e-d1d624200037

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
    HasCyclicHerbrand (unitsRep v w) (completionConj hv) :=
  ⟨Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_cycSub_normHom v w hv hw]; norm_num),
    Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_normHom_cycSub v w hv hw]; norm_num)⟩
end GroundTheory.Global.InfinitePlace
