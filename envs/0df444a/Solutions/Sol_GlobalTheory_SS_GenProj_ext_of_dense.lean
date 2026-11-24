-- Prove2me | solution 1 for GlobalTheory.SS.GenProj.ext_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:16:48.381843+00:00
-- url     : https://prove2.me/submissions/6a2da4d2-9a16-4543-a81a-a3afbe3b0c41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels

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
theorem _root_.solution {W X T Z : Scheme.{0}} (j : W ⟶ X)
    [IsSchemeTheoreticallyDominant j] {m m' : X ⟶ T} (g : T ⟶ Z) [IsSeparated g]
    (h₁ : j ≫ m = j ≫ m') (h₂ : m ≫ g = m' ≫ g) : m = m' := by
  let a : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m
  let b : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m' h₂.symm
  have : IsSeparated (Over.mk g).hom := ‹_›
  let c : Over.mk (j ≫ m ≫ g) ⟶ Over.mk (m ≫ g) := Over.homMk j
  have hc : c ≫ a = c ≫ b := by ext1; exact h₁
  have hk : (equalizer.ι a b).left.ker = ⊥ := by
    have e : (equalizer.lift c hc).left ≫ (equalizer.ι a b).left = j := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    have := (equalizer.lift c hc).left.le_ker_comp (equalizer.ι a b).left
    rw [e] at this
    exact le_bot_iff.mp (this.trans j.ker_eq_bot.le)
  have : IsIso (equalizer.ι a b).left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b).left]
  exact congr($(equalizer.condition a b).left)
end GlobalTheory.SS.GenProj
