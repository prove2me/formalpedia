-- Prove2me | solution 1 for GlobalTheory.ChowHt.Model.blockSphereMean_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:16.149237+00:00
-- url     : https://prove2.me/submissions/fad80d23-c48e-404d-92eb-cb68b9f39b0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sphereLinLog


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
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model
namespace GlobalTheory.ChowHt.Model
theorem _root_.solution {N : ℕ} (c : Fin N → ℂ) (hc : c ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.blockSphereMean 1 N (linForm c) =
      Real.log (Real.sqrt (∑ i, ‖c i‖ ^ 2)) - (harmonic (N - 1) : ℝ) / 2 := by
  have h := (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog N (WithLp.toLp 2 c) (by simpa using hc)).2
  rw [EuclideanSpace.norm_eq] at h
  simp only at h
  rw [← h]
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  rw [← (MeasureTheory.measurePreserving_funUnique (ReciprocityTheory.MultiplicativeHeights.sphereProb N) (Fin 1)).integral_comp']
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [linForm, ReciprocityTheory.MultiplicativeHeights.blockPoint]
end GlobalTheory.ChowHt.Model
