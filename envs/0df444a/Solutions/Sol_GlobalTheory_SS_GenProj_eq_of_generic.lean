-- Prove2me | solution 1 for GlobalTheory.SS.GenProj.eq_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:32:54.686714+00:00
-- url     : https://prove2.me/submissions/6207c6c2-3c6f-4510-ba99-97e77a886496

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels
import Theorems.Thm_GlobalTheory_SS_GenProj_ext_of_dense

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
theorem _root_.solution {S E U X X' A : Scheme.{0}} (i : E ⟶ S) [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    (s : X ⟶ S) (s' : X' ⟶ S) [Flat s] [IsSeparated s'] (p : U ⟶ X) (q : U ⟶ X') [Flat p]
    (hs : p ≫ s = q ≫ s') (j : A ⟶ X) [Mono j] (j' : A ⟶ X')
    (H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U) (t : Z ⟶ E), a ≫ p ≫ s = t ≫ i → ∃ c : Z ⟶ A, c ≫ j = a ≫ p ∧ c ≫ j' = a ≫ q)
    {Z : Scheme.{0}} (a b : Z ⟶ U) (hab : a ≫ p = b ≫ p) : a ≫ q = b ≫ q := by
  have key : pullback.fst p p ≫ q = pullback.snd p p ≫ q := by
    let w := pullback.fst p p ≫ p ≫ s
    have : Flat w := by dsimp only [w]; infer_instance
    refine ext_of_dense (pullback.fst w i) s' ?_ ?_
    · obtain ⟨c₁, h₁, h₁'⟩ := H _ (pullback.fst w i ≫ pullback.fst p p) (pullback.snd w i)
        (by rw [← pullback.condition]; simp [w])
      obtain ⟨c₂, h₂, h₂'⟩ := H _ (pullback.fst w i ≫ pullback.snd p p) (pullback.snd w i)
        (by rw [← pullback.condition, Category.assoc, ← pullback.condition_assoc])
      have e : c₁ = c₂ := by
        rw [← cancel_mono j, h₁, h₂, Category.assoc, Category.assoc, pullback.condition]
      rw [← Category.assoc, ← Category.assoc, ← h₁', ← h₂', e]
    · rw [Category.assoc, Category.assoc, ← hs, pullback.condition_assoc]
  have := congrArg (fun x => pullback.lift a b hab ≫ x) key
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
end GlobalTheory.SS.GenProj
