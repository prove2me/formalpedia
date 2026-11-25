-- Prove2me | solution 1 for GlobalTheory.SharpGradient.rows_le_neg_log_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:47:42.204918+00:00
-- url     : https://prove2.me/submissions/ff1e0510-e1f9-4f06-98ad-7098e57c118b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_det_le_prod_diag
import Theorems.Thm_GlobalTheory_SharpGradient_conj_diag
import Theorems.Thm_GlobalTheory_SharpGradient_det_conj
import Theorems.Thm_GlobalTheory_SharpGradient_posDef_conj
import Theorems.Thm_GlobalTheory_SharpGradient_row_lt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_re_pos_im
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


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
theorem _root_.solution {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    ∑ a, -Real.log (1 - ∑ b, Complex.normSq ((Uᴴ * Z) a b)) ≤
      -Real.log (1 - Z * Zᴴ).det.re := by
  have h := det_le_prod_diag (posDef_conj U hU hZ)
  rw [det_conj U hU] at h
  simp only [conj_diag U hU] at h
  have h2 := Real.log_le_log (ExhA.det_re_pos_im hZ).1 h
  rw [Real.log_prod (fun a _ => (sub_pos.2 (row_lt_one U hU hZ a)).ne')] at h2
  rw [Finset.sum_neg_distrib]
  linarith
end GlobalTheory.SharpGradient
