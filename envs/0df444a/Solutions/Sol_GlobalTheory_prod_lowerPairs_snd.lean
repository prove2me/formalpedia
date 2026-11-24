-- Prove2me | solution 1 for GlobalTheory.prod_lowerPairs_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:55.365976+00:00
-- url     : https://prove2.me/submissions/eeddf9e5-0665-4713-9202-0ad1aff7ae9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetOfBlockTriangularInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (d : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, d p.1.2 = ∏ a, d a ^ (r - 1 - (a : ℕ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1)
    (by simp) (fun p => d p.2), Finset.prod_filter, Fintype.prod_prod_type_right]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [← Fin.card_Ioi a]
  congr 1
  ext c; simp
end GlobalTheory
