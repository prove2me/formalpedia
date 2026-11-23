-- Prove2me | solution 1 for GlobalTheory.CosetQuotient.effectiveEpi_of_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:03.784285+00:00
-- url     : https://prove2.me/submissions/1ab00ea3-639f-4489-8db1-e30a71102acf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.CosetQuotient
universe v u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.CosetQuotient
theorem _root_.solution {X Y : Over S} (f : X ⟶ Y) [EffectiveEpi f.left] :
    EffectiveEpi f := by
  have hw : ∀ {W : Over S} (e : X ⟶ W),
      (∀ {Z : Over S} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) →
      ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ f.left = g₂ ≫ f.left →
        g₁ ≫ e.left = g₂ ≫ e.left := by
    intro W e he Z g₁ g₂ hg
    have h2 : g₂ ≫ X.hom = g₁ ≫ X.hom := by
      rw [← Over.w f, ← Category.assoc, ← hg, Category.assoc]
    have := he (Over.homMk g₁ rfl : Over.mk (g₁ ≫ X.hom) ⟶ X) (Over.homMk g₂ h2)
      (by ext; simpa using hg)
    exact congrArg CommaMorphism.left this
  exact ⟨⟨{
    desc := fun {W} e he => Over.homMk (EffectiveEpi.desc f.left e.left (hw e he)) (by
      rw [← cancel_epi f.left, ← Category.assoc, EffectiveEpi.fac, Over.w e, Over.w f])
    fac := fun {W} e he => by
      ext
      simp [EffectiveEpi.fac]
    uniq := fun {W} e he m hm => by
      ext
      exact EffectiveEpi.uniq f.left e.left (hw e he) m.left (by rw [← Over.comp_left, hm]) }⟩⟩
end GlobalTheory.CosetQuotient
