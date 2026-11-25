-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.natCard_kerModRange_normHom_cycSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:07:09.623526+00:00
-- url     : https://prove2.me/submissions/a46adeca-cd25-4dad-83df-32afae761ef6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Theorems.Thm_GroundTheory_Global_natCard_kerModRange_eq_one
import Theorems.Thm_GroundTheory_Global_InfinitePlace_cycSub_unitsRep_toMul
import Theorems.Thm_GroundTheory_Global_InfinitePlace_normHom_unitsRep_toMul
import Theorems.Thm_GroundTheory_Global_InfinitePlace_exists_conj_eq_mul

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
    Nat.card (KerModRange (normHom (unitsRep v w))
      (cycSub (unitsRep v w) (completionConj hv))) = 1 := by
  apply natCard_kerModRange_eq_one
  intro x hx
  rw [AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, normHom_unitsRep_toMul hv hw] at hx
  have hz : extensionEmbedding w (x.toMul : w.Completion) *
      conj (extensionEmbedding w (x.toMul : w.Completion)) = 1 := by
    rw [← extensionEmbedding_completionConj hv, ← map_mul, hx, map_one]
  obtain ⟨u, hu0, hu⟩ := exists_conj_eq_mul hz
  obtain ⟨y, rfl⟩ := surjective_extensionEmbedding_of_isComplex hw u
  have hy0 : y ≠ 0 := by rintro rfl; exact hu0 (map_zero _)
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rw [cycSub_unitsRep_toMul, toMul_ofMul, Units.val_mk0, div_eq_iff hy0]
  apply (extensionEmbedding w).injective
  rw [extensionEmbedding_completionConj, hu, map_mul]
end GroundTheory.Global.InfinitePlace
