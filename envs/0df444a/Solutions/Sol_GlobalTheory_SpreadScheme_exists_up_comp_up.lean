-- Prove2me | solution 1 for GlobalTheory.SpreadScheme.exists_up_comp_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:37:29.558115+00:00
-- url     : https://prove2.me/submissions/8e7c42a0-9d15-4ec0-92c0-012b257e523d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
import Theorems.Thm_GlobalTheory_SpreadScheme_eq_comp_bcMap
import Theorems.Thm_GlobalTheory_Spread_exists_fg_comp_eq_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.SpreadScheme
open GlobalTheory.Spread GlobalTheory.GlueModels
variable {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {P Q T : Scheme.{0}}
  {p : P ⟶ Sp k} {q : Q ⟶ Sp k} {t : T ⟶ Sp V} {τ : T ⟶ P} {τ' : T ⟶ Q}
namespace GlobalTheory.SpreadScheme
theorem _root_.solution [LocallyOfFiniteType p] [QuasiCompact p]
    (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) {R₁ R₂ : Subalgebra k V} (hR₁ : R₁.FG) (hR₂ : R₂.FG)
    (ψ : pullback p (spMap (algebraMap k R₁)) ⟶ Q) (hψ : ψ ≫ q = pullback.fst _ _ ≫ p)
    (χ : pullback q (spMap (algebraMap k R₂)) ⟶ P) (hχ : χ ≫ p = pullback.fst _ _ ≫ q)
    (hψ' : bcMap p R₁.val ≫ ψ = hτ.isoPullback.inv ≫ τ')
    (hχ' : bcMap q R₂.val ≫ χ = hτ'.isoPullback.inv ≫ τ) :
    ∃ R : Subalgebra k V, R.FG ∧ ∀ (R' : Subalgebra k V) (h₁ : R₁ ≤ R') (h₂ : R₂ ≤ R'), R ≤ R' →
      up h₁ ψ hψ ≫ up h₂ χ hχ = 𝟙 _ := by
  have l₁ : R₁ ≤ R₁ ⊔ R₂ := le_sup_left
  have l₂ : R₂ ≤ R₁ ⊔ R₂ := le_sup_right
  have h : hτ.isoPullback.hom ≫ bcMap p (R₁ ⊔ R₂).val ≫ up l₁ ψ hψ =
      hτ'.isoPullback.hom ≫ bcMap q (R₁ ⊔ R₂).val := by
    apply eq_comp_bcMap hτ'
    · rw [Category.assoc, Category.assoc, up_fst, bcMap_comp_of_eq_assoc p _ _ R₁.val fun _ ↦ rfl, hψ',
        Iso.hom_inv_id_assoc]
    · rw [Category.assoc, Category.assoc, up_snd, bcMap_snd, IsPullback.isoPullback_hom_snd_assoc]
  obtain ⟨R, hle, hR, e⟩ := exists_fg_comp_eq_comp p p (R₁ ⊔ R₂) (hR₁.sup hR₂)
    (up l₁ ψ hψ ≫ up l₂ χ hχ ≫ pullback.fst _ _) (pullback.fst _ _)
    (by rw [Category.assoc, Category.assoc, pullback.condition, up_snd_assoc, up_snd_assoc]) rfl
    (by rw [← cancel_epi hτ.isoPullback.hom, reassoc_of% h, up_fst,
      bcMap_comp_of_eq_assoc q _ _ R₂.val fun _ ↦ rfl, hχ', Iso.hom_inv_id_assoc, bcMap_fst,
      IsPullback.isoPullback_hom_fst])
  refine ⟨R, hR, fun R' h₁ h₂ h₃ ↦ ?_⟩
  apply pullback.hom_ext
  · have e' := congr(bcMap p (Subalgebra.inclusion h₃) ≫ $e)
    rw [bcMap_comp_of_eq_assoc p _ _ (Subalgebra.inclusion (hle.trans h₃)) fun _ ↦ rfl,
      ← up_bcMap_assoc, ← up_bcMap_assoc, bcMap_fst, bcMap_fst, bcMap_fst] at e'
    rw [Category.assoc, Category.id_comp]
    exact e'
  · rw [Category.assoc, up_snd, up_snd, Category.id_comp]
end GlobalTheory.SpreadScheme
