-- Prove2me | solution 1 for GlobalTheory.prod_lowerPairs_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:54.491812+00:00
-- url     : https://prove2.me/submissions/c00c1028-cd4f-4a73-9011-6ed05e4043be

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
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, d p.1.1 = ∏ a, d a ^ (a : ℕ) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1)
    (by simp) (fun p => d p.1), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [← Fin.card_Iio a]
  congr 1
  ext c; simp
end GlobalTheory
