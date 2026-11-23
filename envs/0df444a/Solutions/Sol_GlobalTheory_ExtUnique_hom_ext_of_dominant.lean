-- Prove2me | solution 1 for GlobalTheory.ExtUnique.hom_ext_of_dominant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:11.212682+00:00
-- url     : https://prove2.me/submissions/15ca667b-15b6-4f1d-a3f1-98fc20b84168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
namespace GlobalTheory.ExtUnique
theorem _root_.solution {W X Y Z : Scheme.{u}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) (w : W ⟶ X) [IsSchemeTheoreticallyDominant w] (hw : w ≫ f = w ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let W' : Over Z := Over.mk (w ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let w' : W' ⟶ X' := Over.homMk w
  have : IsSeparated Y'.hom := ‹_›
  have hw' : w' ≫ f' = w' ≫ g' := Over.OverMorphism.ext hw
  have e : (equalizer.lift w' hw').left ≫ (equalizer.ι f' g').left = w := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hk : (equalizer.ι f' g').left.ker = ⊥ := by
    have h₁ := Scheme.Hom.le_ker_comp (equalizer.lift w' hw').left (equalizer.ι f' g').left
    rw [e, w.ker_eq_bot] at h₁
    exact le_bot_iff.1 h₁
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hk
  have c : (equalizer.ι f' g').left ≫ f'.left = (equalizer.ι f' g').left ≫ g'.left := by
    rw [← Over.comp_left, ← Over.comp_left, equalizer.condition]
  exact (cancel_epi _).1 c
end GlobalTheory.ExtUnique
