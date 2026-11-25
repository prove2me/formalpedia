-- Prove2me | solution 1 for GlobalTheory.HL.StTri.descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:33.036476+00:00
-- url     : https://prove2.me/submissions/e509cc2f-21d8-4596-a039-4d9161d5778e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFrameStabilizerActsUnitriangular
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StTri
namespace GlobalTheory.HL.StTri
theorem _root_.solution {E R : Type} [Field E] [CommRing R] [Nontrivial R] (ι : E →+* R) {n m : ℕ}
    (w : Fin m → Fin n → E) (s : Set (Fin m)) (v : Fin n → E)
    (h : (fun i => ι (v i)) ∈ Submodule.span R ((fun a i => ι (w a i)) '' s)) :
    v ∈ Submodule.span E (w '' s) := by
  letI : Algebra E R := ι.toAlgebra
  have hinj : Function.Injective (Algebra.linearMap E R) := ι.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E R)
    (LinearMap.ker_eq_bot.mpr hinj)
  have hg1 : ∀ c : E, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  have hgm : ∀ (a : R) (c : E), g (a * ι c) = c * g a := by
    intro a c
    have : a * ι c = c • a := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul]
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, hv⟩ := h
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨Finsupp.mapRange g (map_zero g) l, ?_, ?_⟩
  · rw [Finsupp.mem_supported'] at hl ⊢
    intro i hi
    simp [hl i hi]
  · funext k
    have hk := congrFun hv k
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hk ⊢
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [← hg1 (v k), ← hk, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgm, Finsupp.mapRange_apply, mul_comm]
end GlobalTheory.HL.StTri
