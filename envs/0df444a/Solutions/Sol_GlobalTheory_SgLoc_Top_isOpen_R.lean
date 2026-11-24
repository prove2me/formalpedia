-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.isOpen_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:28:41.778093+00:00
-- url     : https://prove2.me/submissions/f3efe74a-fb9b-4339-9f09-140668d3e7ec

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Theorems.Thm_GlobalTheory_SgLoc_Top_isOpen_mul_integer
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_topRing
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_integers
import Theorems.Thm_GlobalTheory_SgLoc_Top_mem_R_split
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
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [MeasurableSpace E]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (M : Model F E) :
    IsOpen (M.R : Set E) := by
  have := locE_topRing M.L
  cases hs : M.split with
  | none =>
    have hR : (M.R : Set E) = M.L.O := by simp only [Model.R, hs]
    rw [hR]
    exact (locE_integers M.L).2
  | some g =>
    have := M.L.top
    have := IsModuleTopology.toContinuousAdd F E
    have hec : Continuous (g.e : E → F × F) :=
      IsModuleTopology.continuous_of_linearMap g.e.toLinearEquiv.toLinearMap
    have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
    have hU : IsOpen (((fun x => (g.q : F) * x) '' (𝒪[F] : Set F)) ×ˢ ((fun x => (g.q : F) * x) '' (𝒪[F] : Set F))) :=
      (isOpen_mul_integer hq).prod (isOpen_mul_integer hq)
    have hsub : (g.e : E → F × F) ⁻¹' (((fun x => (g.q : F) * x) '' (𝒪[F] : Set F)) ×ˢ
        ((fun x => (g.q : F) * x) '' (𝒪[F] : Set F))) ⊆ (M.R : Set E) := by
      rintro x ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
      rw [SetLike.mem_coe, mem_R_split M g hs]
      refine ⟨⟨g.q * a, mul_mem g.q.2 ha⟩, ⟨g.q * b, mul_mem g.q.2 hb⟩, ⟨⟨a, ha⟩ - ⟨b, hb⟩, ?_⟩, ?_⟩
      · exact Subtype.ext (by simp [mul_sub])
      · exact Prod.ext h1.symm h2.symm
    have h0 : (0 : E) ∈ (g.e : E → F × F) ⁻¹' (((fun x => (g.q : F) * x) '' (𝒪[F] : Set F)) ×ˢ
        ((fun x => (g.q : F) * x) '' (𝒪[F] : Set F))) := by
      rw [Set.mem_preimage, map_zero]
      exact ⟨⟨0, zero_mem _, mul_zero _⟩, ⟨0, zero_mem _, mul_zero _⟩⟩
    exact AddSubgroup.isOpen_of_mem_nhds M.R.toAddSubgroup (g := 0)
      (Filter.mem_of_superset ((hU.preimage hec).mem_nhds h0) hsub)
end GlobalTheory.SgLoc.Top
