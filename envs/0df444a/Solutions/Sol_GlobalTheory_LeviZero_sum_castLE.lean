-- Prove2me | solution 1 for GlobalTheory.LeviZero.sum_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:58:17.956827+00:00
-- url     : https://prove2.me/submissions/f355e967-0e7f-4c78-9ce6-33b12dc2d6ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
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
namespace GlobalTheory.LeviZero
theorem _root_.solution {M : Type*} [AddCommMonoid M] {m r : ℕ} (h : m ≤ r) (f : Fin r → M) :
    ∑ b : Fin m, f (Fin.castLE h b) = ∑ b : Fin r, if (b : ℕ) < m then f b else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun b _ => Fin.castLE h b) (fun b _ => by simp)
    (fun a _ b _ hab => Fin.castLE_injective h hab) (fun b hb => ?_) (fun _ _ => rfl)
  exact ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, rfl⟩
end GlobalTheory.LeviZero
