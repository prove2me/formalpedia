-- Prove2me | solution 1 for GlobalTheory.exists_opens_range_etale_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:54:31.378723+00:00
-- url     : https://prove2.me/submissions/aa08dda7-e5a7-4757-9f15-43949a07ce48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Theorems.Thm_GlobalTheory_etale_of_comp_of_etale_of_surjective

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
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution :
    ∀ (W X Y : Scheme.{0}) (g : W ⟶ X) (u : X ⟶ Y) [Etale g] [Etale (g ≫ u)]
      [LocallyOfFinitePresentation u],
      ∃ V : X.Opens, (V : Set X) = Set.range g ∧ Etale (V.ι ≫ u) := by
  intro W X Y g u _ _ _
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  let V : X.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  refine ⟨V, rfl, ?_⟩
  have hr : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; exact subset_rfl
  let g' : W ⟶ V := IsOpenImmersion.lift V.ι g hr
  have hg' : g' ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : Etale (g' ≫ V.ι) := by rw [hg']; infer_instance
  have : Etale g' := Etale.of_comp g' V.ι
  have : Surjective g' := by
    refine ⟨fun v => ?_⟩
    obtain ⟨w, hw⟩ : V.ι v ∈ Set.range g := v.2
    refine ⟨w, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg', hw]
  have : Etale (g' ≫ V.ι ≫ u) := by rw [← Category.assoc, hg']; infer_instance
  exact etale_of_comp_of_etale_of_surjective g' (V.ι ≫ u)
end GlobalTheory
