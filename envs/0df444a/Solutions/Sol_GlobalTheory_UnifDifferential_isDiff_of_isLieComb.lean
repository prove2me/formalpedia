-- Prove2me | solution 1 for GlobalTheory.UnifDifferential.isDiff_of_isLieComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:13:22.965658+00:00
-- url     : https://prove2.me/submissions/7ac77d01-7009-41d6-a71d-5a98a1e3f605

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Theorems.Thm_GlobalTheory_UnifDifferential_isDiff_scale
import Theorems.Thm_GlobalTheory_UnifDifferential_isDiff_prod
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
variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A]
namespace GlobalTheory.UnifDifferential
theorem _root_.solution :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g n : ℕ) (u : HolUnif A L g) (W : Fin n → (Fin g → ℂ))
      (v : Fin n → (epsR ℂ ⟶ A)) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A), (∀ i, IsTangent (v i)) →
      (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w := by
  intro A _ L g n u W v c w hv h hw
  rw [(isLieComb_iff c v w).1 hw]
  exact (isDiff_prod u (fun i => c i • W i) _ (fun i => isTan_scale (c i) ((isTan_iff _).2 (hv i)))
    (fun i => isDiff_scale u (h i) (c i))).2
end GlobalTheory.UnifDifferential
