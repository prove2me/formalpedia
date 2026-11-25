-- Prove2me | solution 1 for GlobalTheory.SharpGradient.sharpAt_rhF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:18:41.515639+00:00
-- url     : https://prove2.me/submissions/67089553-af25-4648-aca6-1e32167b0ac6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_SharpAt_of_minorant
import Theorems.Thm_GlobalTheory_SharpGradient_sharpAt_sum
import Theorems.Thm_P2M_GlobalTheory_SharpGradient_sharpAt_sum__57325bd9992d
import Theorems.Thm_GlobalTheory_SharpGradient_sharpAt_ball
import Theorems.Thm_GlobalTheory_SharpGradient_row_lt_one
import Theorems.Thm_GlobalTheory_SharpGradient_rows_le_neg_log_det
import Theorems.Thm_GlobalTheory_SharpGradient_exists_unitary_rows
import Theorems.Thm_GlobalTheory_SharpGradient_rhF_eq_sum_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_Zt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SharpGradient
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) : SharpAt (rhF X x0) z ξ := by
  have hpd : ∀ y ∈ OmF X x0, ∀ τ, (1 - ExF.Zt X y τ * (ExF.Zt X y τ)ᴴ).PosDef :=
    fun y hy => (ExF.mem_OmF_iff X x0 ho y).1 hy
  choose U hU he using fun τ => exists_unitary_rows (hpd z hz τ)
  have hS : SharpAt (fun y => ∑ τ, ∑ a, -Real.log (1 - ∑ b,
      Complex.normSq (((U τ)ᴴ * ExF.Zt X y τ) a b))) z ξ := by
    refine sharpAt_sum' fun τ => sharpAt_sum fun a => ?_
    refine sharpAt_ball (g := fun b y => ((U τ)ᴴ * ExF.Zt X y τ) a b) ξ (fun b => ?_)
      (row_lt_one _ (hU τ) (hpd z hz τ) a)
    simp only [Matrix.mul_apply]
    exact (ContDiff.sum fun c _ => contDiff_const.mul (ExF.cd_Zt X τ c b)).contDiffAt.of_le
      (WithTop.coe_le_coe.2 le_top)
  refine hS.of_minorant ((ExF.rhF_contDiffAt X x0 ho hz).of_le (WithTop.coe_le_coe.2 le_top)) ?_ ?_
  · filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with y hy
    rw [rhF_eq_sum_re X x0 ho hy]
    exact Finset.sum_le_sum fun τ _ => rows_le_neg_log_det _ (hU τ) (hpd y hy τ)
  · rw [rhF_eq_sum_re X x0 ho hz]
    exact Finset.sum_congr rfl fun τ _ => he τ
end GlobalTheory.SharpGradient
