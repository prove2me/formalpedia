-- Prove2me | solution 1 for GlobalTheory.SS.FinUnion.le_of_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:41:10.134421+00:00
-- url     : https://prove2.me/submissions/9331f79b-6360-4d9e-a3d4-927f77967016

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslates
import Theorems.Thm_GlobalTheory_SS_FinUnion_mem_of_closed
import Theorems.Thm_GlobalTheory_SS_FinUnion_dense_res
import Theorems.Thm_GlobalTheory_SS_FinUnion_mem_range_j
import Theorems.Thm_GlobalTheory_SS_FinUnion_ext_apply
import Theorems.Thm_GlobalTheory_SS_FinUnion_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_FinUnion_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_FinUnion_twist_j
import Theorems.Thm_GlobalTheory_SS_FinUnion_exists_move
import Theorems.Thm_GlobalTheory_SS_FinUnion_law_split
import Theorems.Thm_GlobalTheory_SS_CompatCrit_mem_range_j
import Theorems.Thm_GlobalTheory_SS_GI_twist_j
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_Translates_twist_j
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FinUnion
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
variable [GrpObj A] [IsCommMonObj A]
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.SS.FinUnion
theorem _root_.solution [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] {M G : Model R A} (hM : Strict M)
    (m : M.Y ⊗ M.Y ⟶ G.Y) (hm : (M.prod M).j ≫ m.left = (μ[A]).left ≫ G.j) (a : 𝟙_ (Over (Sp K)) ⟶ A)
    (ha : GenIso M M (transl a).hom) (hc : Compat (M.twist (transl a)) G) : (M.twist (transl a)).Le G := by
  obtain ⟨W, g, h, hg, hh, eg, eh, hcl⟩ := hc
  have hsurj : Function.Surjective g.left := by
    intro y
    by_cases hy : y ∈ M.sp
    swap
    · obtain ⟨x, rfl⟩ := mem_range_j (M.twist (transl a)) y hy
      exact ⟨W.j x, by rw [← Scheme.Hom.comp_apply, eg]⟩
    obtain ⟨z₀, hz₀, O, σ, hO, hσ, -⟩ := (hM.2 false y hy).2
    obtain ⟨x, hx, V, τ, hV, hτ, -⟩ := ha
    have hy' : M.Y.hom (pullback.snd M.Y.hom M.Y.hom z₀) = IsLocalRing.closedPoint R := by
      have : M.Y.hom ((snd M.Y M.Y).left z₀) = IsLocalRing.closedPoint R := by rw [hz₀]; exact hy
      exact this
    obtain ⟨z, hzO, hz, hzV⟩ := exists_move M.Y.hom M.Y.hom O z₀ hO V
      (by rw [hy']; exact hM.1.1.2) x hV (by rw [hy']; exact hx)
    let Ω : (M.prod M).Y.left.Opens := O ⊓ (fst M.Y M.Y).left ⁻¹ᵁ V
    let U : Over (Sp R) := Over.mk (Ω.ι ≫ (M.Y ⊗ M.Y).hom)
    let i : U ⟶ M.Y ⊗ M.Y := Over.homMk Ω.ι rfl
    let a₁ : Ω.toScheme ⟶ V.toScheme := (fst M.Y M.Y).left.resLE V Ω inf_le_right
    have e₁ : a₁ ≫ V.ι = Ω.ι ≫ (fst M.Y M.Y).left := Scheme.Hom.resLE_comp_ι _ _
    let a₂ : Ω.toScheme ⟶ O.toScheme := Scheme.homOfLE _ inf_le_left
    have e₂ : a₂ ≫ O.ι = Ω.ι := Scheme.homOfLE_ι _ _
    let φ₁ : U ⟶ M.Y := Over.homMk (a₁ ≫ τ) (by
      change (a₁ ≫ τ) ≫ M.Y.hom = Ω.ι ≫ (M.Y ⊗ M.Y).hom
      rw [Category.assoc, hτ.1, ← Category.assoc, e₁, Category.assoc, Over.w])
    let φ₂ : U ⟶ M.Y ⊗ M.Y := Over.homMk (a₂ ≫ σ) (by
      change (a₂ ≫ σ) ≫ (M.prod M).Y.hom = Ω.ι ≫ (M.prod M).Y.hom
      rw [Category.assoc, hσ.1, ← Category.assoc, e₂])
    let t := (M.prod M).j ∣_ Ω
    let w := ((M.prod M).j ⁻¹ᵁ Ω).ι
    have et : t ≫ Ω.ι = w ≫ (M.prod M).j := morphismRestrict_ι _ _
    have c₁ : (t ≫ a₁) ≫ τ = (w ≫ (fst A A).left) ≫ (transl a).hom.left ≫ M.j :=
      ext_apply hτ _ _ (by
        rw [Category.assoc, e₁, ← Category.assoc, et, Category.assoc, Category.assoc]
        exact congrArg (w ≫ ·) (prod_j_fst M M))
    have c₂ : (t ≫ a₂) ≫ σ = w ≫ (shear A false).left ≫ (M.prod M).j :=
      ext_apply hσ _ _ (by rw [Category.assoc, e₂, et])
    have c₃ : t ≫ (lift φ₁ (φ₂ ≫ snd M.Y M.Y)).left =
        w ≫ (lift (fst A A ≫ (transl a).hom) (shear A false ≫ snd A A)).left ≫ (M.prod M).j := by
      apply pullback.hom_ext
      · change (t ≫ _) ≫ (fst M.Y M.Y).left = (w ≫ _) ≫ (fst M.Y M.Y).left
        rw [Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, Category.assoc]
        erw [prod_j_fst M M]
        rw [← Over.comp_left_assoc, lift_fst]
        simp only [Category.assoc, Over.comp_left] at c₁ ⊢
        exact c₁
      · change (t ≫ _) ≫ (snd M.Y M.Y).left = (w ≫ _) ≫ (snd M.Y M.Y).left
        rw [Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, Category.assoc]
        erw [prod_j_snd M M]
        rw [← Over.comp_left_assoc, lift_snd]
        have := congrArg (· ≫ (snd M.Y M.Y).left) c₂
        simp only [Category.assoc] at this
        erw [prod_j_snd M M] at this
        simp only [Category.assoc, Over.comp_left]
        exact this
    obtain ⟨v, hv, -⟩ := mem_of_closed g h (i ≫ snd M.Y M.Y) (lift φ₁ (φ₂ ≫ snd M.Y M.Y) ≫ m) t
      (dense_res (M.prod M) Ω) (w ≫ (snd A A).left ≫ (transl a).hom.left ≫ W.j)
      (by
        simp only [Category.assoc]
        rw [eg, twist_j, ← prod_j_snd M M, ← Category.assoc, ← et, Category.assoc]
        rfl)
      (by
        simp only [Category.assoc]
        rw [eh, Over.comp_left, ← Category.assoc, c₃]
        simp only [Category.assoc]
        erw [hm]
        rw [← Over.comp_left_assoc, law_split, Over.comp_left_assoc])
      ⟨z, hzO, hzV⟩
    exact ⟨v, hv.trans (hz.trans hz₀)⟩
  have : Surjective g.left := ⟨hsurj⟩
  have : IsIso g.left := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hg, this⟩
  have : IsIso ((Over.forget _).map g) := this
  have : IsIso g := isIso_of_reflects_iso g (Over.forget _)
  have e : g.left ≫ (inv g ≫ h).left = h.left := by rw [← Over.comp_left, IsIso.hom_inv_id_assoc]
  refine ⟨inv g ≫ h, ?_, ?_⟩
  · rw [← IsIso.eq_inv_comp] at e
    rw [e]; infer_instance
  · rw [← eg, Category.assoc, e, eh]
end GlobalTheory.SS.FinUnion
