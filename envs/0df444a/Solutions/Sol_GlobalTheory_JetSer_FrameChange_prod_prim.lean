-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.prod_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:23:27.117062+00:00
-- url     : https://prove2.me/submissions/87179e26-0626-4e7c-82bb-ba1014b41bb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
variable {G}
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution {T : Over S} (w : G ⟶ G) (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k, h (x.left ≫ primφ w k) ^ primε k = h x.left * (lamV h x (x ≫ w))⁻¹ := by
  have e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w) := (MonObj.comp_mul _ _ _).trans (by simp)
  have e₄ : x ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  rw [Fin.prod_univ_five]
  show h (x.left ≫ 𝟙 _) ^ (1 : ℤ) * h (x ≫ (𝟙 G * w)).left ^ (-1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (1 : ℤ) *
    h (x ≫ w).left ^ (1 : ℤ) * h (x ≫ (1 : G ⟶ G)).left ^ (-1 : ℤ) = _
  rw [e₁, e₄, Category.comp_id]
  simp only [zpow_neg, zpow_one, lamV]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.JetSer.FrameChange
