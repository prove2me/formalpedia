-- Prove2me | solution 1 for GlobalTheory.UnifDifferential.pullFn_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:25.999398+00:00
-- url     : https://prove2.me/submissions/10da5022-b70e-4946-8759-dcca8ca6e7da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp IsTan fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.SqZero
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.UnifDifferential
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
  {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
namespace GlobalTheory.UnifDifferential
theorem _root_.solution (φ : S →ₐ[R] S') (y : sp (R₀ := R) S ⟶ A) (y' : sp (R₀ := R) S' ⟶ A)
    (e : y' = Chart.spMap φ ≫ y) (U : A.left.Opens) (h : ⊤ ≤ y.left ⁻¹ᵁ U)
    (h' : ⊤ ≤ y'.left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    pullFn y' U h' f = φ (pullFn y U h f) := by
  subst e
  have e : (Chart.spMap φ ≫ y).left.appLE U ⊤ h' =
      y.left.appLE U ⊤ h ≫ (Spec.map (CommRingCat.ofHom (φ : S →+* S'))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (φ : S →+* S'))) y.left U ⊤ ⊤ h le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((y.left.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (φ : S →+* S')))
  unfold pullFn
  rw [e]
  exact e2
end GlobalTheory.UnifDifferential
