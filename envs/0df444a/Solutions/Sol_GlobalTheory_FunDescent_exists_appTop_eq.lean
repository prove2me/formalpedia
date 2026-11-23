-- Prove2me | solution 1 for GlobalTheory.FunDescent.exists_appTop_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:00:51.84828+00:00
-- url     : https://prove2.me/submissions/d1f61eed-1182-4a6f-b1c3-cc0cee6e0432

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Theorems.Thm_GlobalTheory_FunDescent_hom_ext
import Theorems.Thm_GlobalTheory_FunDescent_exists_hom
import Theorems.Thm_GlobalTheory_FunDescent_comp_appTop_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FunDescent
namespace GlobalTheory.FunDescent
theorem _root_.solution {X Y : Scheme.{0}} (π : X ⟶ Y) [EffectiveEpi π] (f : Γ(X, ⊤))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X), g₁ ≫ π = g₂ ≫ π →
      g₁.appTop.hom f = g₂.appTop.hom f) :
    ∃ a, π.appTop.hom a = f := by
  obtain ⟨g, rfl⟩ := exists_hom f
  have H : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ g = g₂ ≫ g := by
    intro Z g₁ g₂ e
    apply hom_ext
    rw [comp_appTop_apply, comp_appTop_apply]
    exact hf Z g₁ g₂ e
  refine ⟨(EffectiveEpi.desc π g H).appTop.hom coord, ?_⟩
  rw [← comp_appTop_apply, EffectiveEpi.fac]
end GlobalTheory.FunDescent
