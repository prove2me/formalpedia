-- Prove2me | solution 1 for GlobalTheory.SharpGradient.neg_log_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:02.139961+00:00
-- url     : https://prove2.me/submissions/4b74ea09-bf59-4a57-9bd3-ac415b28645d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_exists_unitary_rows
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgC_trace_mul_conjTranspose_re
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
theorem _root_.solution {p q : ℕ} {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef)
    (hs : ∑ a, ∑ b, Complex.normSq (Z a b) ≤ 1 / 2) :
    -Real.log (1 - Z * Zᴴ).det.re ≤ 2 * ∑ a, ∑ b, Complex.normSq (Z a b) := by
  obtain ⟨U, hU, he⟩ := exists_unitary_rows hZ
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  have hF : ∑ a, ∑ b, Complex.normSq ((Uᴴ * Z) a b) = ∑ a, ∑ b, Complex.normSq (Z a b) := by
    rw [← RgC.trace_mul_conjTranspose_re, ← RgC.trace_mul_conjTranspose_re,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', Matrix.one_mul]
  rw [he, ← hF, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  set t := ∑ b, Complex.normSq ((Uᴴ * Z) a b) with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have ht1 : t ≤ 1 / 2 := by
    refine le_trans ?_ (hF ▸ hs)
    exact Finset.single_le_sum (f := fun a => ∑ b, Complex.normSq ((Uᴴ * Z) a b))
      (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
  have h1 : 0 < 1 - t := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : (1 - t)⁻¹ ≤ 1 + 2 * t := by
    rw [inv_le_iff_one_le_mul₀ h1]
    nlinarith
  linarith
end GlobalTheory.SharpGradient
