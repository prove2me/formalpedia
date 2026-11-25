-- Prove2me | solution 1 for GroundTheory.Global.mixedTraceForm_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:23.013981+00:00
-- url     : https://prove2.me/submissions/9e661357-6f7f-4842-bb9c-58c841727ade

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Theorems.Thm_GroundTheory_Global_mapComplexCoord_apply
import Theorems.Thm_GroundTheory_Global_sqrtTwoSMulComplex_apply
import Theorems.Thm_GroundTheory_Global_sqrtTwoSMulConj_apply
import Theorems.Thm_GroundTheory_Global_inner_toMixed_symm
import Theorems.Thm_P2M_GroundTheory_Global_mixedTraceForm_apply__be78fc251b6f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (x y : mixedSpace K) :
    mixedTraceForm K x y = ⟪mixedToEuclidean K x, mixedToEuclideanConj K y⟫ := by
  rw [mixedTraceForm_apply', mixedToEuclidean, mixedToEuclideanConj,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, inner_toMixed_symm]
  simp only [mapComplexCoord_apply, sqrtTwoSMulComplex_apply, sqrtTwoSMulConj_apply]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hs : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have : conj ((√2 : ℝ) • x.2 w) * ((√2 : ℝ) • conj (y.2 w)) =
      ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) * conj (x.2 w * y.2 w) := by
    rw [Complex.real_smul, Complex.real_smul, map_mul, map_mul, Complex.conj_ofReal]
    ring
  rw [this, hs]
  simp
end GroundTheory.Global
