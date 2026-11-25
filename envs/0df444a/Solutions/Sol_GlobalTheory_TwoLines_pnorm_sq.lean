-- Prove2me | solution 1 for GlobalTheory.TwoLines.pnorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:10:05.023458+00:00
-- url     : https://prove2.me/submissions/2b008756-51a4-4269-9de1-53767bea1ae4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Theorems.Thm_GlobalTheory_TwoLines_dmin_0
import Theorems.Thm_GlobalTheory_TwoLines_dmin_1
import Theorems.Thm_GlobalTheory_TwoLines_colSq_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution {X : Data E 2} (hG : X.Gm = 1) {x : Frame X.Ψ 2} (hx : x ∈ X.dom) {la : Wt X.Ψ 2}
    {m : ℕ} (h0 : ∀ τ, la τ 0 = m) (h1 : ∀ τ, la τ 1 = 0) (P : Frame X.Ψ 2 → ℂ) :
    X.pnorm la P x ^ 2 = ‖P x‖ ^ 2 / (∏ τ, colSq x τ) ^ m := by
  unfold Data.pnorm
  rw [mul_pow, div_eq_mul_inv, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hp := colSq_pos (hx τ).1
  rw [Fin.prod_univ_two, h0, h1, hG]
  have e1 : (0 : Fin 2).succ = 1 := rfl
  have e2 : (0 : Fin 2).castSucc = 0 := rfl
  rw [e1, e2, dmin_0, dmin_1]
  simp only [Int.cast_zero, neg_zero, zero_div, Real.rpow_zero, mul_one, div_one, Complex.norm_real,
    Real.norm_of_nonneg hp.le, Int.cast_natCast]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_natCast, ← Real.rpow_neg hp.le]
  congr 1
  push_cast; ring
end GlobalTheory.TwoLines
