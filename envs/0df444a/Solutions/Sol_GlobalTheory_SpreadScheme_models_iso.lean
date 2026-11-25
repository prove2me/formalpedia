-- Prove2me | solution 1 for GlobalTheory.SpreadScheme.models_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:57:56.062307+00:00
-- url     : https://prove2.me/submissions/5915de0e-5c2b-465f-89ad-7212837b57a1

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
import Theorems.Thm_GlobalTheory_SpreadScheme_exists_up_comp_up
import Theorems.Thm_GlobalTheory_Spread_exists_fg_comp_eq
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
theorem _root_.solution [LocallyOfFinitePresentation p] [QuasiSeparated p] [QuasiCompact p]
    [LocallyOfFinitePresentation q] [QuasiSeparated q] [QuasiCompact q]
    (hτ : IsPullback τ t p (spMap (algebraMap k V))) (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) :
    ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))),
      R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ →
        σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by
  obtain ⟨R₁, ψ, hR₁, hψ, hψ'⟩ := exists_fg_comp_eq p q (hτ.isoPullback.inv ≫ τ') (by
    rw [Category.assoc, hτ'.w, ← hτ.w, IsPullback.isoPullback_inv_fst_assoc])
  obtain ⟨R₂, χ, hR₂, hχ, hχ'⟩ := exists_fg_comp_eq q p (hτ'.isoPullback.inv ≫ τ) (by
    rw [Category.assoc, hτ.w, ← hτ'.w, IsPullback.isoPullback_inv_fst_assoc])
  obtain ⟨R₃, hR₃, e₃⟩ := exists_up_comp_up hτ hτ' hR₁ hR₂ ψ hψ χ hχ hψ' hχ'
  obtain ⟨R₄, hR₄, e₄⟩ := exists_up_comp_up hτ' hτ hR₂ hR₁ χ hχ ψ hψ hχ' hψ'
  let R : Subalgebra k V := (R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)
  have l₁ : R₁ ≤ R := le_sup_left.trans le_sup_left
  have l₂ : R₂ ≤ R := le_sup_right.trans le_sup_left
  refine ⟨R, ⟨up l₁ ψ hψ, up l₂ χ hχ, e₃ R l₁ l₂ (le_sup_left.trans le_sup_right),
    e₄ R l₂ l₁ (le_sup_right.trans le_sup_right)⟩, (hR₁.sup hR₂).sup (hR₃.sup hR₄), up_snd l₁ ψ hψ,
    fun σ h₁ h₂ ↦ ?_⟩
  rw [eq_comp_bcMap hτ R σ h₁ h₂, Category.assoc]
  change _ ≫ _ ≫ up l₁ ψ hψ ≫ _ = _
  rw [up_fst, bcMap_comp_of_eq_assoc p _ _ R₁.val fun _ ↦ rfl, hψ', Iso.hom_inv_id_assoc]
end GlobalTheory.SpreadScheme
