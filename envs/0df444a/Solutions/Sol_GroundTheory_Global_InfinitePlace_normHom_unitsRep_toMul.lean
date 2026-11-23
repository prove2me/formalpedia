-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.normHom_unitsRep_toMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:02.596117+00:00
-- url     : https://prove2.me/submissions/83be8710-c768-4160-9031-bdec26e77d1c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Theorems.Thm_GroundTheory_Global_InfinitePlace_unitsRep_toMul
import Theorems.Thm_GroundTheory_Global_normHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.normHom_apply



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
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ) :
    ((normHom (unitsRep v w) x).toMul : w.Completion) =
      (x.toMul : w.Completion) * completionConj (w := w) hv (x.toMul : w.Completion) := by
  classical
  rw [normHom_apply, univ_eq_one_completionConj hv hw,
    Finset.sum_pair (completionConj_ne_one hv hw).symm, toMul_add, Units.val_mul, unitsRep_toMul,
    unitsRep_toMul, AlgEquiv.one_apply]
end GroundTheory.Global.InfinitePlace
