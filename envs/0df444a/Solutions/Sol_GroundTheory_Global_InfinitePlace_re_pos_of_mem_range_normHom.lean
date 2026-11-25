-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.re_pos_of_mem_range_normHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:17.629501+00:00
-- url     : https://prove2.me/submissions/17ad0357-1302-4a7c-9b81-e4a15b2d1d22

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Theorems.Thm_GroundTheory_Global_InfinitePlace_normHom_unitsRep_toMul

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
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (hv : v.IsReal) (hw : w.IsComplex)
    {x : Additive w.Completionˣ} (hx : x ∈ (normHom (unitsRep v w)).range) :
    0 < (extensionEmbedding w (x.toMul : w.Completion)).re := by
  obtain ⟨y, rfl⟩ := hx
  rw [normHom_unitsRep_toMul hv hw, map_mul, extensionEmbedding_completionConj, Complex.mul_conj,
    Complex.ofReal_re]
  exact Complex.normSq_pos.2 ((map_ne_zero _).2 (Units.ne_zero _))
end GroundTheory.Global.InfinitePlace
