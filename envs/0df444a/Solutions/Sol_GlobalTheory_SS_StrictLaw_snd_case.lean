-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.snd_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:56:53.299825+00:00
-- url     : https://prove2.me/submissions/b8eebd68-e408-489c-9be3-8e72a8cb12da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
import Theorems.Thm_GlobalTheory_SS_StrictLaw_fibre_preirr
import Theorems.Thm_GlobalTheory_SS_StrictLaw_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_StrictLaw_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_StrictLaw_geomIrr
import Theorems.Thm_GlobalTheory_SS_StrictLaw_exists_pt
import Theorems.Thm_GlobalTheory_SS_StrictLaw_ext_pt
import Theorems.Thm_GlobalTheory_SS_StrictLaw_isPullback_prod
import Theorems.Thm_GlobalTheory_SS_extends_id


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
variable [IsDomain R] [IsLocalRing R] [IsFractionRing R K]
  [IsAlgClosed (IsLocalRing.ResidueField R)]
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution (M : Model R A) (hM : M.Irr) (hMM : (M.prod M).Irr) (f f' : A ⊗ A ⟶ A ⊗ A)
    (hf : f ≫ fst A A = fst A A) (hf' : f' ≫ snd A A = snd A A)
    (hff : f ≫ snd A A = f' ≫ fst A A)
    (h : GenIso (M.prod M) (M.prod M) f) (h' : GenIso (M.prod M) (M.prod M) f') :
    ∃ T : Set M.Y.left, IsOpen T ∧ (M.sp ∩ T).Nonempty ∧ ∀ V : Set M.Y.left, IsOpen V →
      ∀ x ∈ M.sp, x ∈ T → x ∈ V → ∃ z, (pr₂ M M).left z = x ∧ Good M f V z := by
  obtain ⟨y, hy, U, g, hyU, he, hg⟩ := h
  obtain ⟨y', hy', U', g', hyU', he', hg'⟩ := h'
  have := M.smooth
  have hp := (isPullback_prod M M).flip
  have ho : UniversallyOpen (pr₂ M M).left :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨y₀, hy₀, hy₀U⟩ := hMM.2 _ _ U.2 U'.2 ⟨y, hy, hyU⟩ ⟨y', hy', hyU'⟩
  have hUU : IsOpen ((U : Set (M.prod M).Y.left) ∩ U') := U.2.inter U'.2
  refine ⟨(pr₂ M M).left '' (U ∩ U'), (pr₂ M M).left.isOpenMap _ hUU,
    ⟨_, ?_, y₀, hy₀U, rfl⟩, ?_⟩
  · show M.Y.hom _ = _
    rw [← Scheme.Hom.comp_apply, Over.w]
    exact hy₀
  rintro V hV x hx ⟨w, hwU, hw⟩ hxV
  have := geomIrr M hM (M.Y.hom x) hx
  have hF := fibre_preirr hp x
  have hc : ∀ u, (pr₁ M M).left (g u) = (pr₁ M M).left (U.ι u) := fun u =>
    ext_pt (Q := M) he (extends_id _ U) (pr₁ M M) (pr₁ M M) (by
      rw [prod_j_fst, ← Category.assoc, ← Over.comp_left, hf]; simp) u u rfl
  have hc' : ∀ u, (pr₂ M M).left (g' u) = (pr₂ M M).left (U'.ι u) := fun u =>
    ext_pt (Q := M) he' (extends_id _ U') (pr₂ M M) (pr₂ M M) (by
      rw [prod_j_snd, ← Category.assoc, ← Over.comp_left, hf']; simp) u u rfl
  have hO : IsOpen ((pr₁ M M).left ⁻¹' V) := hV.preimage (pr₁ M M).left.continuous
  obtain ⟨d, hd, hd'⟩ := Scheme.exists_preimage_of_isPullback hp x x rfl
  have hd2 : ((pr₂ M M).left ⁻¹' {x} ∩ (pr₁ M M).left ⁻¹' V).Nonempty :=
    ⟨d, hd, show (pr₁ M M).left d ∈ V from hd' ▸ hxV⟩
  obtain ⟨u', hu, hux, hgu⟩ := exists_pt (pr₂ M M).left x hF U'.ι g' U'.ι.continuous
    g'.isOpenEmbedding.isOpenMap hc' ((U ∩ U') ∩ (pr₁ M M).left ⁻¹' V) _ (hUU.inter hO) hO
    (fun z hz => ⟨⟨z, hz.1.2⟩, rfl⟩) (hF _ _ hUU hO ⟨w, hw, hwU⟩ hd2) hd2
  let u : U.toScheme := ⟨U'.ι u', hu.1.1⟩
  have huu : U.ι u = U'.ι u' := rfl
  have hc'' : (pr₂ M M).left (g u) = (pr₁ M M).left (g' u') :=
    ext_pt (Q := M) he he' (pr₂ M M) (pr₁ M M) (by
      rw [prod_j_fst, prod_j_snd, ← Category.assoc, ← Over.comp_left, hff, Over.comp_left,
        Category.assoc]) u u' huu
  exact ⟨_, hux, U, g, u, he, hg, huu, hu.2, hux ▸ hxV, (hc u) ▸ hu.2, hc'' ▸ hgu⟩
end GlobalTheory.SS.StrictLaw
