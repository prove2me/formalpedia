-- Prove2me | solution 1 for GlobalTheory.SS.GenProj.exists_openImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:12.391609+00:00
-- url     : https://prove2.me/submissions/97819e9b-95a0-4529-833b-a13e0bdaf757

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels
import Theorems.Thm_GlobalTheory_SS_GenProj_exists_image

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GenProj
namespace GlobalTheory.SS.GenProj
theorem _root_.solution {U X X' : Scheme.{0}} (p : U ⟶ X) (q : U ⟶ X') [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q]
    (H : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p = b ≫ p ↔ a ≫ q = b ≫ q) :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme) (h : V.toScheme ⟶ X'), p' ≫ V.ι = p ∧ Flat p' ∧ Surjective p' ∧
      p' ≫ h = q ∧ IsOpenImmersion h := by
  obtain ⟨V, p', hp, _, _, _⟩ := exists_image p
  obtain ⟨V', q', hq, _, _, _⟩ := exists_image q
  have H' : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p' = b ≫ p' ↔ a ≫ q' = b ≫ q' := by
    intro Z a b
    rw [← cancel_mono V.ι, ← cancel_mono V'.ι]
    simpa [hp, hq] using H Z a b
  let u := EffectiveEpi.desc p' q' (fun a b h => (H' _ a b).1 h)
  let v := EffectiveEpi.desc q' p' (fun a b h => (H' _ a b).2 h)
  have hu : p' ≫ u = q' := EffectiveEpi.fac _ _ _
  have hv : q' ≫ v = p' := EffectiveEpi.fac _ _ _
  have : IsIso u := ⟨v, by rw [← cancel_epi p', ← Category.assoc, hu, hv, Category.comp_id],
    by rw [← cancel_epi q', ← Category.assoc, hv, hu, Category.comp_id]⟩
  exact ⟨V, p', u ≫ V'.ι, hp, ‹_›, ‹_›, by rw [← Category.assoc, hu, hq], inferInstance⟩
end GlobalTheory.SS.GenProj
