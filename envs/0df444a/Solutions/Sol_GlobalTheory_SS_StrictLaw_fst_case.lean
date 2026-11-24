-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.fst_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:57:14.776802+00:00
-- url     : https://prove2.me/submissions/e13c94c5-efa8-433b-99b3-ffe30d0eefc9

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
theorem _root_.solution (M : Model R A) (hM : M.Irr) (f : A ⊗ A ⟶ A ⊗ A) (hf : f ≫ fst A A = fst A A)
    (h : GenIso (M.prod M) (M.prod M) f) :
    ∃ T : Set M.Y.left, IsOpen T ∧ (M.sp ∩ T).Nonempty ∧ ∀ V : Set M.Y.left, IsOpen V →
      ∀ x ∈ M.sp, x ∈ T → x ∈ V → ∃ z, (pr₁ M M).left z = x ∧ Good M f V z := by
  obtain ⟨y, hy, U, g, hyU, he, hg⟩ := h
  have := M.smooth
  have hp := isPullback_prod M M
  have ho : UniversallyOpen (pr₁ M M).left :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  refine ⟨(pr₁ M M).left '' U, (pr₁ M M).left.isOpenMap _ U.2, ⟨_, hy, y, hyU, rfl⟩, ?_⟩
  rintro V hV x hx ⟨w, hwU, hw⟩ hxV
  have := geomIrr M hM (M.Y.hom x) hx
  have hF := fibre_preirr hp x
  have hc : ∀ u, (pr₁ M M).left (g u) = (pr₁ M M).left (U.ι u) := fun u =>
    ext_pt (Q := M) he (extends_id _ U) (pr₁ M M) (pr₁ M M) (by
      rw [prod_j_fst, ← Category.assoc, ← Over.comp_left, hf]; simp) u u rfl
  have hO : IsOpen ((pr₂ M M).left ⁻¹' V) := hV.preimage (pr₂ M M).left.continuous
  obtain ⟨d, hd, hd'⟩ := Scheme.exists_preimage_of_isPullback hp x x rfl
  have hd2 : ((pr₁ M M).left ⁻¹' {x} ∩ (pr₂ M M).left ⁻¹' V).Nonempty :=
    ⟨d, hd, show (pr₂ M M).left d ∈ V from hd' ▸ hxV⟩
  obtain ⟨u, hu, hux, hgu⟩ := exists_pt (pr₁ M M).left x hF U.ι g U.ι.continuous
    g.isOpenEmbedding.isOpenMap hc (U ∩ (pr₂ M M).left ⁻¹' V) _ (U.2.inter hO) hO
    (fun z hz => ⟨⟨z, hz.1⟩, rfl⟩) (hF _ _ U.2 hO ⟨w, hw, hwU⟩ hd2) hd2
  exact ⟨_, hux, U, g, u, he, hg, rfl, hux ▸ hxV, hu.2, ((hc u).trans hux) ▸ hxV, hgu⟩
end GlobalTheory.SS.StrictLaw
