-- Prove2me | solution 1 for GlobalTheory.AbelianQuotient.exists_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:01:58.354789+00:00
-- url     : https://prove2.me/submissions/71b53882-ec58-4866-bbf1-7c8d5bd4273c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.AbelianQuotient
variable {S : Scheme.{0}}
namespace GlobalTheory.AbelianQuotient
theorem _root_.solution {X Y Z : Over S} (p : X ⟶ Y) [Flat p.left] [Surjective p.left]
    [QuasiCompact p.left] (f : X ⟶ Z)
    (h : ∀ (W : Over S) (a b : W ⟶ X), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    ∃ β : Y ⟶ Z, p ≫ β = f := by
  have hc : ∀ {W : Scheme.{0}} (g g' : W ⟶ X.left), g ≫ p.left = g' ≫ p.left →
      g ≫ f.left = g' ≫ f.left := by
    intro W g g' hg
    have hw : g' ≫ X.hom = g ≫ X.hom := by
      rw [← Over.w p, ← Category.assoc, ← hg, Category.assoc]
    have := h (Over.mk (g ≫ X.hom)) (Over.homMk g rfl) (Over.homMk g' hw)
      (Over.OverMorphism.ext hg)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac p.left f.left hc
  exact ⟨Over.homMk (EffectiveEpi.desc p.left f.left hc) (by
    rw [← cancel_epi p.left, ← Category.assoc, hfac, Over.w, Over.w]),
    Over.OverMorphism.ext hfac⟩
end GlobalTheory.AbelianQuotient
