-- Prove2me | solution 1 for GlobalTheory.LeviZero.HasJet.conj_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:39.499678+00:00
-- url     : https://prove2.me/submissions/a0546239-7000-42f0-a63d-a7fe3d34d83a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
import Theorems.Thm_GlobalTheory_LeviZero_coord_diff
import Theorems.Thm_GlobalTheory_LeviZero_wd_coord
import Theorems.Thm_GlobalTheory_LeviZero_coord_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_of_differentiableAt
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
variable {n : ℕ}
variable {ξ : Fin n → ℂ} {x : V n}
namespace GlobalTheory.LeviZero
namespace HasJet
theorem _root_.solution (m : Fin n) :
    HasJet ξ 0 (fun z : V n => conj (z m)) (tJ * cJ (conj (ξ m))) := by
  have hd : ∀ y, DifferentiableAt ℝ (fun z : V n => z m) y := fun y =>
    (coord_diff m y).restrictScalars ℝ
  have h0 : ∀ k, wdb n k (fun z : V n => conj (z m)) = fun _ => if m = k then 1 else 0 := fun k =>
    funext fun y => by rw [wdb_conj (hd y), wd_coord]; split_ifs <;> simp
  refine ⟨(Complex.conjCLE.contDiff.comp (coord_cd m)).contDiffAt, by simp [tJ], ?_, ?_, ?_⟩
  · simp [dDir, wd_conj (hd _), wdb_of_differentiableAt (coord_diff m _), tJ, cJ,
      DualNumber.snd_mul]
  · simp [dbDir, h0, tJ, cJ, DualNumber.snd_mul]
  · simp [leviV, h0, wd, tJ, cJ, DualNumber.snd_mul]
end HasJet
end GlobalTheory.LeviZero
