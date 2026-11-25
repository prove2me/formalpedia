-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.mem_range_normHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:16.93803+00:00
-- url     : https://prove2.me/submissions/3751a67f-26dd-4802-bb2b-8565468d7ac3

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
theorem _root_.solution (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ)
    (hx : completionConj (w := w) hv (x.toMul : w.Completion) = x.toMul)
    (hpos : 0 < (extensionEmbedding w (x.toMul : w.Completion)).re) :
    x ∈ (normHom (unitsRep v w)).range := by
  have hreal : extensionEmbedding w (x.toMul : w.Completion) =
      ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ) := by
    have h := extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)
    rw [hx] at h
    exact (Complex.conj_eq_iff_re.1 h.symm).symm
  set r := (extensionEmbedding w (x.toMul : w.Completion)).re
  obtain ⟨a, ha⟩ := surjective_extensionEmbedding_of_isComplex hw (Real.sqrt r : ℂ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Complex.ofReal_eq_zero, Real.sqrt_eq_zero hpos.le] at ha
    exact hpos.ne' ha
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  apply (extensionEmbedding w).injective
  rw [normHom_unitsRep_toMul hv hw, toMul_ofMul, Units.val_mk0, map_mul,
    extensionEmbedding_completionConj, ha, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hpos.le, ← hreal]
end GroundTheory.Global.InfinitePlace
