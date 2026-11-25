-- Prove2me | solution 1 for GlobalTheory.ChartCount.card_strictLower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:53:58.527171+00:00
-- url     : https://prove2.me/submissions/908e67d5-c634-4f13-9e63-0d5d130d92c9

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TamagawaSpecialUnitary_320f37a25cd91d38
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PhaseFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotallyRealDegreeAndChartDimensionEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
open GlobalTheory GlobalTheory.ChartCount
namespace GlobalTheory.ChartCount
theorem _root_.solution (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (a b : Fin r) => b < a)),
    Fintype.card_sigma]
  have h : ∀ a : Fin r, Fintype.card {b : Fin r // b < a} = (a : ℕ) := by
    intro a
    rw [Fintype.card_subtype]
    have : Finset.univ.filter (fun b : Fin r => b < a) = Finset.Iio a := by ext; simp
    rw [this, Fin.card_Iio]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]
end GlobalTheory.ChartCount
