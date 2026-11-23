-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.jetCoeff_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:56.644802+00:00
-- url     : https://prove2.me/submissions/bfb15cd2-3d85-450a-b0c9-355a3e6da661

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_jetCoeff_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution {κ : Type} (m : ℕ) (p : MvPolynomial κ R) :
    jetCoeff R R' κ m (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R R') p) := by
  have : (jetCoeff R R' κ m).comp (Ideal.Quotient.mkₐ R _) =
      (Ideal.Quotient.mkₐ R _).comp (MvPolynomial.mapAlgHom (Algebra.ofId R R')) := by
    apply MvPolynomial.algHom_ext
    intro j
    refine (jetCoeff_zR m j).trans ?_
    simp
  exact AlgHom.congr_fun this p
end GlobalTheory.ChartBaseChange
