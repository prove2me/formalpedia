-- Prove2me | solution 1 for GlobalTheory.dirPolyDeriv_eq_sum_coeff_taylorDir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:33.293633+00:00
-- url     : https://prove2.me/submissions/dbe250ba-0ee3-4369-9219-3a31addf6895

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_dirPolyDeriv_eq_sum
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero



set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (u : σ → W) {f g : W → ℂ}
namespace GlobalTheory
theorem _root_.solution (P : MvPolynomial σ ℂ) (f : W → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u f 0 = ∑ m ∈ P.support,
      P.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m (taylorDir u f) := by
  rw [dirPolyDeriv_eq_sum]
  simp only [dirPolyDeriv_monomial_eq_coeff, mul_assoc]
end GlobalTheory
