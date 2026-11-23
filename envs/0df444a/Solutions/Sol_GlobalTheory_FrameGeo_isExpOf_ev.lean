-- Prove2me | solution 1 for GlobalTheory.FrameGeo.isExpOf_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:48.843628+00:00
-- url     : https://prove2.me/submissions/32b3e565-4e35-410e-ba91-5c83c43917ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_ev_eq
import Theorems.Thm_GlobalTheory_FramePull_map_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameGeo
open GlobalTheory.FramePull ReciprocityTheory.ChartRestriction.G.TB
variable {R : Type} [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace GlobalTheory.FrameGeo
theorem _root_.solution {m : ℕ} {a : Fin m → Pt R 1 d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    {w : PS R m d} {f : PS k m d} (f0 : constantCoeff f = 0) (hw : FB.toK k w = FB.expS k f) :
    IsExpOf (ev a w) (ev (fun j i => FB.toK k (a j i)) f) := by
  have ha' : ∀ j i, constantCoeff (FB.toK k (a j i)) = 0 := fun j i => by simp [FB.toK, ha]
  refine ⟨by rw [constantCoeff_ev_eq ha', f0], ?_⟩
  have e1 : FB.toK k (ev a w) = ev (fun j i => FB.toK k (a j i)) (FB.toK k w) := map_ev_eq _ ha w
  rw [e1, hw]
  unfold ev FB.expS
  exact WickVanishing.subst_exp (fun p : Fin m × Fin d => FB.toK k (a p.1 p.2)) (fun p => ha' p.1 p.2) f0
end GlobalTheory.FrameGeo
