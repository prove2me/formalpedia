-- Prove2me | solution 1 for GlobalTheory.SharpGradient.det_le_prod_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:07.129663+00:00
-- url     : https://prove2.me/submissions/832c3e94-3baa-42ab-8406-5cea59ce29a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_re_pos_im
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgB_amgm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
namespace GlobalTheory.SharpGradient
theorem _root_.solution {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef) :
    A.det.re ≤ ∏ i, (A i i).re := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hd : ∀ i, 0 < A i i := fun i => hA.diag_pos
  have hre : ∀ i, ((A i i).re : ℂ) = A i i := fun i =>
    Complex.ext (by simp) (by simp [(Complex.lt_def.1 (hd i)).2.symm])
  have hD : (Matrix.diagonal fun i => A i i).PosDef := Matrix.posDef_diagonal_iff.2 hd
  have h := RgB.amgm hm hA hD
  have hinv : (Matrix.diagonal fun i => A i i)⁻¹ = Matrix.diagonal fun i => (A i i)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd i).ne'
  have htr : (A * (Matrix.diagonal fun i => A i i)⁻¹).trace.re = m := by
    rw [hinv]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, mul_inv_cancel₀ (hd _).ne']
    simp
  have hdet : (Matrix.diagonal fun i => A i i).det.re = ∏ i, (A i i).re := by
    rw [Matrix.det_diagonal, ← Complex.ofReal_re (∏ i, (A i i).re), Complex.ofReal_prod]
    simp only [hre]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [htr, hdet, div_self hmR.ne', mul_one] at h
  have hp : 0 ≤ ∏ i, (A i i).re := Finset.prod_nonneg fun i _ => (Complex.lt_def.1 (hd i)).1.le
  exact (Real.rpow_le_rpow_iff (ExhA.det_re_pos_im hA).1.le hp (inv_pos.2 hmR)).1 h
end GlobalTheory.SharpGradient
