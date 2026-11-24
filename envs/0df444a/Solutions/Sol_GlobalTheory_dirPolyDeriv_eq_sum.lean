-- Prove2me | solution 1 for GlobalTheory.dirPolyDeriv_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:21.259334+00:00
-- url     : https://prove2.me/submissions/42ffadf8-67df-46af-84ae-dfff900193cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
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
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory
theorem _root_.solution (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x = ∑ m ∈ P.support,
      P.coeff m * ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u F x := by
  simp only [dirPolyDeriv_monomial_one]
  rfl
end GlobalTheory
