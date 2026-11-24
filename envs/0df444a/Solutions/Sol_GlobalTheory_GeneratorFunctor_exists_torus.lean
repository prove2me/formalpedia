-- Prove2me | solution 1 for GlobalTheory.GeneratorFunctor.exists_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:16.948809+00:00
-- url     : https://prove2.me/submissions/031221e1-7461-448c-aa3b-d8d23481348a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


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
open GlobalTheory
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GeneratorFunctor
theorem _root_.solution (S : Scheme.{0}) (κ : Type) :
    ∃ (T : Scheme.{0}) (p : T ⟶ S) (t : κ → Γ(T, ⊤)ˣ),
      (∀ (Z : Scheme.{0}) (c : Z ⟶ S) (v : κ → Γ(Z, ⊤)ˣ), ∃ g : Z ⟶ T, g ≫ p = c ∧
        ∀ k, g.appTop.hom (t k).val = (v k).val) ∧
      ∀ (Z : Scheme.{0}) (g g' : Z ⟶ T), g ≫ p = g' ≫ p →
        (∀ k, g.appTop.hom (t k).val = g'.appTop.hom (t k).val) → g = g' := by
  refine ⟨(splitTorus S (FreeAbelianGroup κ)).left, (splitTorus S (FreeAbelianGroup κ)).hom,
    fun k => charUnit S _ (FreeAbelianGroup.of k), fun Z c v => ?_, fun Z g g' h hk => ?_⟩
  · let φ : FreeAbelianGroup κ →+ Additive Γ(Z, ⊤)ˣ :=
      FreeAbelianGroup.lift fun k => Additive.ofMul (v k)
    obtain ⟨g, hg⟩ := (splitTorusPointsEquiv S (FreeAbelianGroup κ) (Over.mk c)).surjective
      (AddMonoidHom.toMultiplicativeLeft φ)
    refine ⟨g.left, Over.w g, fun k => ?_⟩
    refine (splitTorusPointsEquiv_val S _ (Over.mk c) g _).symm.trans ?_
    rw [hg]
    simp [φ]
  · let Z' : Over S := Over.mk (g' ≫ (splitTorus S (FreeAbelianGroup κ)).hom)
    let a : Z' ⟶ splitTorus S (FreeAbelianGroup κ) := Over.homMk g h
    let a' : Z' ⟶ splitTorus S (FreeAbelianGroup κ) := Over.homMk g' rfl
    have : a = a' := by
      apply (splitTorusPointsEquiv S (FreeAbelianGroup κ) Z').injective
      apply AddMonoidHom.toMultiplicativeLeft.symm.injective
      refine FreeAbelianGroup.lift_ext _ _ fun k => ?_
      apply Additive.toMul.injective
      apply Units.ext
      exact ((splitTorusPointsEquiv_val S _ Z' a _).trans (hk k)).trans
        (splitTorusPointsEquiv_val S _ Z' a' _).symm
    exact congrArg (·.left) this
end GlobalTheory.GeneratorFunctor
