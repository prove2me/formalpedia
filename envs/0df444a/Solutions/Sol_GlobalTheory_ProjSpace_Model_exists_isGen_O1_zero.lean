-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.exists_isGen_O1_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:08:22.978436+00:00
-- url     : https://prove2.me/submissions/4d9250c8-67cb-45cc-8efe-9ed893f2ae90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_GlobalTheory_ProjSpace_O1_g_eq_ratioUnit_chart_inf
import Theorems.Thm_GlobalTheory_ProjSpace_ratioUnit_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace GlobalTheory.ProjSpace.Model
variable {R : Type} [CommRing R] {N : ℕ}
namespace GlobalTheory.ProjSpace.Model
theorem _root_.solution : ∃ t : (O1 R 0).Gen, t.IsGen := by
  refine ⟨⟨fun _ => 1⟩, fun (i j : Fin 1) => ?_⟩
  obtain rfl : i = j := Subsingleton.elim _ _
  rw [O1_g_eq_ratioUnit_chart_inf, ratioUnit_self, map_one]
  exact (one_mul _).symm
end GlobalTheory.ProjSpace.Model
