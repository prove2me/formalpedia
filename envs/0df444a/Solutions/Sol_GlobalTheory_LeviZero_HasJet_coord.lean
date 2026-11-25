-- Prove2me | solution 1 for GlobalTheory.LeviZero.HasJet.coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:55:44.40647+00:00
-- url     : https://prove2.me/submissions/ad36507e-6d4c-4301-a89e-1d2a632ef99b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
import Theorems.Thm_GlobalTheory_LeviZero_coord_diff
import Theorems.Thm_GlobalTheory_LeviZero_wd_coord
import Theorems.Thm_GlobalTheory_LeviZero_coord_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
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
theorem _root_.solution (m : Fin n) : HasJet ξ 0 (fun z : V n => z m) (sJ * cJ (ξ m)) := by
  have h0 : ∀ k, wdb n k (fun z : V n => z m) = fun _ => 0 := fun k =>
    funext fun y => wdb_of_differentiableAt (coord_diff m y)
  refine ⟨(coord_cd m).contDiffAt, by simp [sJ], ?_, ?_, ?_⟩
  · simp [dDir, wd_coord, sJ, cJ, DualNumber.snd_mul]
  · simp [dbDir, h0, sJ, cJ, DualNumber.snd_mul]
  · simp [leviV, h0, wd, sJ, cJ, DualNumber.snd_mul]
end HasJet
end GlobalTheory.LeviZero
