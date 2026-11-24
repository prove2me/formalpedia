-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.isoAt_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:23:17.166613+00:00
-- url     : https://prove2.me/submissions/a11d58b4-c654-49db-b229-a9f5a76e0f6a

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
import Theorems.Thm_GlobalTheory_SS_StrictLaw_extends_comp

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
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution {M N : Model R A} {M' N' : Model R A'} {f : A ⟶ A'}
    (i : N.Y.left ⟶ M.Y.left) (i' : N'.Y.left ⟶ M'.Y.left) [IsOpenImmersion i] [IsOpenImmersion i']
    (hi : i ≫ M.Y.hom = N.Y.hom) (hi' : i' ≫ M'.Y.hom = N'.Y.hom)
    (hj : N.j ≫ i = M.j) (hj' : N'.j ≫ i' = M'.j)
    {U : M.Y.left.Opens} {g : U.toScheme ⟶ M'.Y.left} [IsOpenImmersion g] (h : Extends M M' f U g)
    (z : N.Y.left) (u : U.toScheme) (hu : U.ι u = i z) (hg : g u ∈ Set.range i') :
    IsoAt N N' f z := by
  let W : N.Y.left.Opens := i ⁻¹ᵁ (U.ι ''ᵁ (g ⁻¹ᵁ i'.opensRange))
  have h1 : Set.range (W.ι ≫ i) ⊆ Set.range U.ι := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, -, hv⟩ := w.2
    exact ⟨v, hv⟩
  let l := IsOpenImmersion.lift U.ι (W.ι ≫ i) h1
  have hl : l ≫ U.ι = W.ι ≫ i := IsOpenImmersion.lift_fac _ _ _
  have h2 : Set.range (l ≫ g) ⊆ Set.range i' := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv', hv⟩ := w.2
    have : U.ι (l w) = U.ι v := by
      rw [← Scheme.Hom.comp_apply, hl]; exact hv.symm
    rw [Scheme.Hom.comp_apply, U.ι.isOpenEmbedding.injective this]
    exact hv'
  let m := IsOpenImmersion.lift i' (l ≫ g) h2
  have hm : m ≫ i' = l ≫ g := IsOpenImmersion.lift_fac _ _ _
  refine ⟨W, m, ⟨u, hg, hu⟩, ⟨?_, ?_⟩, inferInstance⟩
  · rw [← hi', ← hi, ← Category.assoc, hm, Category.assoc, h.1, ← Category.assoc, hl, Category.assoc]
  · rw [← cancel_mono i', Category.assoc, hm, ← Category.assoc,
      extends_comp h (N.j ⁻¹ᵁ W).ι _ (by rw [Category.assoc, hl, ← hj, morphismRestrict_ι_assoc])]
    simp only [Category.assoc, hj']
end GlobalTheory.SS.StrictLaw
