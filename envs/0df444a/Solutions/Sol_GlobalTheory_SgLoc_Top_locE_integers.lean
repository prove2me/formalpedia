-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.locE_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:15:03.824635+00:00
-- url     : https://prove2.me/submissions/302fec3c-f8c0-4054-9715-034c74f54fdf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Theorems.Thm_GlobalTheory_SgLoc_Top_localField_isOpen_integer
import Theorems.Thm_GlobalTheory_SgLoc_Top_isCompact_mul_integer
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_exists_coords
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_homeo
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_topRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    IsCompact (L.O : Set E) ∧ IsOpen (L.O : Set E) := by
  obtain ⟨ψ, D, hD0, h1, h2⟩ := locE_exists_coords L
  obtain ⟨h, hh⟩ := locE_homeo L ψ
  have := locE_topRing L
  have hAo : IsOpen (h '' ((𝒪[F] : Set F) ×ˢ (𝒪[F] : Set F))) :=
    h.isOpenMap _ ((localField_isOpen_integer F).prod (localField_isOpen_integer F))
  have hAO : h '' ((𝒪[F] : Set F) ×ˢ (𝒪[F] : Set F)) ⊆ (L.O : Set E) := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    rw [hh]
    exact h1 p hp1 hp2
  have h0 : (0 : E) ∈ h '' ((𝒪[F] : Set F) ×ˢ (𝒪[F] : Set F)) :=
    ⟨0, ⟨zero_mem _, zero_mem _⟩, by rw [hh, map_zero]⟩
  have hOo : IsOpen (L.O : Set E) :=
    AddSubgroup.isOpen_of_mem_nhds L.O.toAddSubgroup (g := 0) (Filter.mem_of_superset (hAo.mem_nhds h0) hAO)
  have hOc : IsClosed (L.O : Set E) := AddSubgroup.isClosed_of_isOpen L.O.toAddSubgroup hOo
  have h2ne : (2 : F) ≠ 0 := two_ne_zero
  have hBc : IsCompact (h '' (((fun x => (2 : F)⁻¹ * x) '' (𝒪[F] : Set F)) ×ˢ
      ((fun x => (2 * D)⁻¹ * x) '' (𝒪[F] : Set F)))) :=
    ((isCompact_mul_integer _).prod (isCompact_mul_integer _)).image h.continuous
  have hOB : (L.O : Set E) ⊆ h '' (((fun x => (2 : F)⁻¹ * x) '' (𝒪[F] : Set F)) ×ˢ
      ((fun x => (2 * D)⁻¹ * x) '' (𝒪[F] : Set F))) := by
    intro x hx
    have hx' := h2 (ψ.symm x) (by rw [LinearEquiv.apply_symm_apply]; exact hx)
    refine ⟨ψ.symm x, ⟨⟨2 * (ψ.symm x).1, hx'.1, ?_⟩, ⟨2 * D * (ψ.symm x).2, hx'.2, ?_⟩⟩, ?_⟩
    · field_simp
    · field_simp
    · rw [hh, LinearEquiv.apply_symm_apply]
  exact ⟨hBc.of_isClosed_subset hOc hOB, hOo⟩
end GlobalTheory.SgLoc.Top
