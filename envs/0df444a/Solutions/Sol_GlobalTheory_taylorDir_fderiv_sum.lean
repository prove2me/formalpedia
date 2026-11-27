-- Prove2me | solution 1 for GlobalTheory.taylorDir_fderiv_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:42:04.087886+00:00
-- url     : https://prove2.me/submissions/24e845e5-a58e-4171-b31b-af786971bed4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_taylorDir_sum
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
theorem _root_.solution (hf : AnalyticAt ℂ f 0) (a : σ → ℂ) :
    taylorDir u (fun z => fderiv ℂ f z (∑ i, a i • u i)) =
      ∑ i, a i • MvPowerSeries.pderiv ℂ i (taylorDir u f) := by
  simp only [map_sum, map_smul]
  rw [taylorDir_sum u _ (F := fun i z => a i • fderiv ℂ f z (u i))
    fun i _ => (analyticAt_fderiv_apply hf (u i)).const_smul (c := a i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← taylorDir_fderiv u hf, ← taylorDir_smul u _ (analyticAt_fderiv_apply hf (u i))]
  rfl
end GlobalTheory
