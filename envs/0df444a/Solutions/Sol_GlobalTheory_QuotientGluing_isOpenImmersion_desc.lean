-- Prove2me | solution 1 for GlobalTheory.QuotientGluing.isOpenImmersion_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:30:31.624118+00:00
-- url     : https://prove2.me/submissions/e1de4d02-67f5-4598-bbcf-2284290904c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientOfFiniteGroup
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_IsAffineQuotient_exists_preimage_eq
import Theorems.Thm_GlobalTheory_IsAffineQuotient_of_isPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.QuotientGluing
variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}}
namespace GlobalTheory.QuotientGluing
theorem _root_.solution {T T' Y Y' : Scheme.{0}} {σ : G →* Aut T} {σ' : G →* Aut T'}
    {q : T ⟶ Y} {q' : T' ⟶ Y'} (h : IsAffineQuotient σ q) (h' : IsAffineQuotient σ' q')
    (m : T ⟶ T') [IsOpenImmersion m] (hm : ∀ g, (σ g).hom ≫ m = m ≫ (σ' g).hom)
    (k : Y ⟶ Y') (hk : q ≫ k = m ≫ q') : IsOpenImmersion k := by
  obtain ⟨W, hW⟩ := h'.exists_preimage_eq (U := m.opensRange) (fun g ↦ by
    rintro _ ⟨x, rfl⟩
    exact ⟨(σ g).hom x, congr($(hm g) x)⟩)
  have hr : Set.range (m ≫ q') ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    have : m x ∈ q' ⁻¹ᵁ W := hW ▸ ⟨x, rfl⟩
    exact ⟨⟨q' (m x), this⟩, rfl⟩
  let l : T ⟶ W := IsOpenImmersion.lift W.ι (m ≫ q') hr
  have hl : l ≫ W.ι = m ≫ q' := IsOpenImmersion.lift_fac _ _ _
  have H : IsPullback l m W.ι q' :=
    IsOpenImmersion.isPullback _ _ _ _ hl.symm (by rw [Scheme.Opens.opensRange_ι, hW])
  have hq : IsAffineQuotient σ l := h'.of_isPullback H.flip hm fun g ↦ by
    rw [← cancel_mono W.ι, Category.assoc, hl, reassoc_of% hm, h'.comp_eq]
  have : k = (h.uniqueIso hq).hom ≫ W.ι := h.hom_ext (by simp [hk, hl])
  rw [this]
  infer_instance
end GlobalTheory.QuotientGluing
