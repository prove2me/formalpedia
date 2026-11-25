-- Prove2me | solution 1 for GlobalTheory.LeviZero.jet_nM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:35:50.714521+00:00
-- url     : https://prove2.me/submissions/34cf9f66-455f-4ff2-8a3b-8193fecf1e6a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
import Theorems.Thm_GlobalTheory_LeviZero_HasJet_coord
import Theorems.Thm_GlobalTheory_LeviZero_cJ_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
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
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace GlobalTheory.LeviZero
theorem _root_.solution (ξ : Fin (nd X) → ℂ) (τ : X.Ψ) (a b : Fin r) :
    HasJet ξ 0 (fun z => ExF.nM X z τ a b) ((if a = b then 1 else 0) + sJ * cH (zMat X ξ τ a b)) := by
  simp only [ExF.nM, mat, nmat, zMat, Matrix.of_apply]
  by_cases h : b < a
  · simp only [dif_pos h, if_neg h.ne', zero_add]
    exact HasJet.coord _
  · simp only [dif_neg h, map_zero, mul_zero, add_zero]
    have := HasJet.const (ξ := ξ) (x := 0) (if a = b then 1 else 0)
    rw [cJ_eq] at this
    split_ifs at this ⊢ <;> simpa using this
end GlobalTheory.LeviZero
