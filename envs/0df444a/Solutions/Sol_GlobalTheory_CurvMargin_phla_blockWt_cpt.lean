-- Prove2me | solution 1 for GlobalTheory.CurvMargin.phla_blockWt_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:23:53.142384+00:00
-- url     : https://prove2.me/submissions/971427ce-be4e-462b-9335-bccb7b264f83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PhlaBlockWtCpt
import Theorems.Thm_GlobalTheory_CurvMargin_tele_tail
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_Lm_last_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_phla_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.CurvMargin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.CurvMargin
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    {z : V (nd X)} (hz : z ∈ OmF X x0) :
    phla X (blockWt X) (cpt X x0 z) = rhF X x0 z := by
  rw [IW.phla_eq X hz, rhF, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set x := cpt X x0 z
  let L' : ℕ → ℝ := fun k => if h : k < r + 1 then IW.Lm X x τ ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have hk : ∀ i : Fin r, ((blockWt X τ i : ℤ) : ℝ) = if (i : ℕ) < X.p0 then (0 : ℝ) else 1 :=
    fun i => by unfold blockWt; split_ifs <;> simp
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 ho z τ
  have hLp : L' X.p0 = Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ := by
    simp only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]; rfl
  simp_rw [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if i < X.p0 then (0 : ℝ) else 1) * (L' (i + 1) - L' i)) r, tele_tail L' X.p0 r X.p0_le,
    hLr, hLp, zero_sub]
end GlobalTheory.CurvMargin
