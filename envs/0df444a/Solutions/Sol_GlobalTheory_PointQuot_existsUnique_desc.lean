-- Prove2me | solution 1 for GlobalTheory.PointQuot.existsUnique_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:11.890641+00:00
-- url     : https://prove2.me/submissions/6b651947-faed-4e32-98ef-55b192cc001f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.PointQuot
variable {S : Scheme.{0}}
namespace GlobalTheory.PointQuot
theorem _root_.solution {A B Y : Over S} (q : A ⟶ B) [Flat q.left] [Surjective q.left]
    [QuasiCompact q.left] (f : A ⟶ Y)
    (hf : ∀ {Z : Over S} (g g' : Z ⟶ A), g ≫ q = g' ≫ q → g ≫ f = g' ≫ f) :
    ∃! f' : B ⟶ Y, q ≫ f' = f := by
  have hc : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ A.left), g ≫ q.left = g' ≫ q.left →
      g ≫ f.left = g' ≫ f.left := by
    intro Z g g' h
    have hw : g' ≫ A.hom = g ≫ A.hom := by
      rw [← Over.w q, ← Category.assoc, ← h, Category.assoc]
    have := hf (Z := Over.mk (g ≫ A.hom))
      (Over.homMk g rfl) (Over.homMk g' hw) (Over.OverMorphism.ext h)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac q.left f.left hc
  let β : B ⟶ Y := Over.homMk (EffectiveEpi.desc q.left f.left hc) (by
    rw [← cancel_epi q.left, ← Category.assoc, hfac, Over.w, Over.w])
  have hβ : q ≫ β = f := Over.OverMorphism.ext hfac
  have : Epi q := Over.epi_of_epi_left q
  exact ⟨β, hβ, fun β' h' => by rw [← cancel_epi q, h', hβ]⟩
end GlobalTheory.PointQuot
