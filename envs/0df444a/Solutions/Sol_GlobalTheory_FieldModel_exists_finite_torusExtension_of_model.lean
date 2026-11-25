-- Prove2me | solution 1 for GlobalTheory.FieldModel.exists_finite_torusExtension_of_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:36:27.118865+00:00
-- url     : https://prove2.me/submissions/00ccb371-94f3-4f59-9a48-71fb83a47104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomDescendsToSubfieldContainingFinsetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Theorems.Thm_GlobalTheory_FieldModel_spMap_comp
import Theorems.Thm_GlobalTheory_FieldModel_exists_baseChange
import Theorems.Thm_GlobalTheory_FieldModel_sq_fst
import Theorems.Thm_GlobalTheory_FieldModel_sq_snd
import Theorems.Thm_GlobalTheory_FieldModel_isPullback_sq
import Theorems.Thm_GlobalTheory_FieldModel_sq_comp
import Theorems.Thm_GlobalTheory_FieldModel_isPullback_unit
import Theorems.Thm_GlobalTheory_FieldModel_bcMap_comp
import Theorems.Thm_GlobalTheory_T_group_structure_descends_along_pullback
import Theorems.Thm_GlobalTheory_T_hom_descends_to_subfield_containing_finset_alt
import Theorems.Thm_GlobalTheory_T_splitTorus_extension_descends_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.FieldModel.sq_fst
attribute [reassoc] GlobalTheory.FieldModel.sq_snd

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FieldModel
variable {K : Type} [Field K]
namespace GlobalTheory.FieldModel
theorem _root_.solution {k k₀ K : Type} [Field k] [Field k₀] [Field K] {σ : k →+* K}
    {α₀ : k →+* k₀} {σ₀ : k₀ →+* K} (e₀ : σ₀.comp α₀ = σ) (G : Over (Sp k)) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsSeparated G.hom]
    (T : TorusExtension ((Over.pullback (spMap σ)).obj G)) {B₀ : Over (Sp k₀)} {φ₀ : T.B.left ⟶ B₀.left}
    (H₀ : IsPullback φ₀ T.B.hom B₀.hom (spMap σ₀)) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (ρ : k₀ →+* k₁) (β : k₁ →+* K),
      β.comp α = σ → β.comp ρ = σ₀ → ρ.comp α₀ = α →
      s ⊆ Set.range β → Nonempty (TorusExtension ((Over.pullback (spMap α)).obj G)) := by
  let _ := T.grpB
  let _ := T.addCommGroup
  have := T.isAbelian.proper
  have HG := isGrpPullback_pullback G (spMap σ)
  obtain ⟨g₀, eg₀, Hg₀⟩ := exists_baseChange (X := (Over.pullback (spMap σ)).obj G) (X₀ := G)
    (spMap_comp e₀) HG.1
  have lB : LocallyOfFiniteType T.B.hom := inferInstance
  have cG : QuasiCompact ((Over.pullback (spMap σ)).obj G).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.hom _))
  have sG : QuasiSeparated ((Over.pullback (spMap σ)).obj G).hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd G.hom _))
  have lG : LocallyOfFiniteType ((Over.pullback (spMap σ)).obj G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))
  have pBB : IsProper (T.B ⊗ T.B).hom := inferInstanceAs (IsProper (pullback.fst T.B.hom T.B.hom ≫ T.B.hom))
  obtain ⟨sm, hm⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K σ₀ _ _ _ _ _ _ (isPullback_sq H₀) H₀ inferInstance inferInstance lB μ[T.B]
  obtain ⟨si, hi⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K σ₀ _ _ _ _ _ _ H₀ H₀ inferInstance inferInstance lB ι[T.B]
  obtain ⟨se, he⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K σ₀ _ _ _ _ _ _ (isPullback_unit _) H₀
    (inferInstanceAs (QuasiCompact (𝟙 (Sp K)))) (inferInstanceAs (QuasiSeparated (𝟙 (Sp K)))) lB η[T.B]
  obtain ⟨sq', hq⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K σ₀ _ _ _ _ _ _ Hg₀ H₀ cG sG lB T.q
  obtain ⟨st, ht⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k K σ _ _ _ _ _ _ (SplitTorus.isPullback_bcMap (spMap σ) T.X) HG.1
    inferInstance inferInstance lG T.i
  refine ⟨sm ∪ (si ∪ (se ∪ (sq' ∪ st))), by simp, fun k₁ _ α ρ β hαβ hρ hρα hs => ?_⟩
  simp only [Set.union_subset_iff] at hs
  obtain ⟨bm, bi, be, bq, bt⟩ := hs
  obtain ⟨φ₁, eφ, H₁⟩ := exists_baseChange (spMap_comp hρ) H₀
  have P₁ : IsPullback (pullback.fst B₀.hom (spMap ρ)) ((Over.pullback (spMap ρ)).obj B₀).hom B₀.hom (spMap ρ) :=
    .of_hasPullback _ _
  have HG₁ := isGrpPullback_pullback G (spMap α)
  obtain ⟨g₁, eg₁, Hg₁⟩ := exists_baseChange (X := (Over.pullback (spMap σ)).obj G) (X₀ := G)
    (spMap_comp hαβ) HG.1
  obtain ⟨χ, eχ, Hχ⟩ := exists_baseChange (X := (Over.pullback (spMap α)).obj G) (X₀ := G)
    (spMap_comp hρα) HG₁.1
  have egχ : g₁ ≫ χ = g₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      exact ((congrArg _ eχ).trans eg₁).trans eg₀.symm
    · change _ ≫ ((Over.pullback (spMap α₀)).obj G).hom = _ ≫ ((Over.pullback (spMap α₀)).obj G).hom
      rw [Category.assoc, Hχ.w, Hg₀.w, Hg₁.w_assoc, spMap_comp hρ]
  have gp : IsGrpPullback _ ((Over.pullback (spMap α)).obj G) (spMap β) g₁ :=
    HG₁.cancel (by rw [eg₁, spMap_comp hαβ]; exact HG) Hg₁.w
  obtain ⟨m₁, hm₁⟩ := hm k₁ ρ β hρ bm _ _ (sq H₁.w) _ φ₁ _ (isPullback_sq P₁) P₁ (sq_comp eφ _ _ _) eφ
    (isPullback_sq H₁).w H₁.w
  obtain ⟨i₁, hi₁⟩ := hi k₁ ρ β hρ bi _ _ φ₁ _ φ₁ _ P₁ P₁ eφ eφ H₁.w H₁.w
  obtain ⟨e₁, he₁⟩ := he k₁ ρ β hρ be (𝟙_ _) _ (spMap β) _ φ₁ _ (isPullback_unit (spMap ρ)) P₁ (spMap_comp hρ) eφ
    (isPullback_unit (spMap β)).w H₁.w
  obtain ⟨q₁, hq₁⟩ := hq k₁ ρ β hρ bq _ _ g₁ _ φ₁ _ Hχ P₁ egχ eφ Hg₁.w H₁.w
  obtain ⟨t₁, ht₁⟩ := ht k₁ α β hαβ bt _ _ (SplitTorus.bcMap (spMap β) T.X) _ g₁ _
    (SplitTorus.isPullback_bcMap (spMap α) T.X) HG₁.1 (bcMap_comp (spMap_comp hαβ) _) eg₁
    (SplitTorus.bcMap_hom _ _) Hg₁.w
  obtain ⟨gB, ab, gpB⟩ := GlobalTheory.T.group_structure_descends_along_pullback k₁ K β T.B _ φ₁ T.isAbelian H₁ m₁ i₁ e₁ _ (sq_fst _) (sq_snd _) hm₁ hi₁ he₁
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := GlobalTheory.T.splitTorus_extension_descends_alt k₁ K β _ T.B _ _ T.X g₁ φ₁ gp gpB T.q T.i q₁ t₁ hq₁ ht₁ T.q_hom
    T.q_flat T.q_surjective T.q_quasiCompact T.i_hom T.isKernel
  exact ⟨
    { X := T.X
      free := T.free
      finite := T.finite
      B := _
      grpB := gB
      isAbelian := ab
      q := q₁
      q_hom := c₁
      q_flat := c₂
      q_surjective := c₃
      q_quasiCompact := c₄
      i := t₁
      i_hom := c₅
      isKernel := c₆ }⟩
end GlobalTheory.FieldModel
