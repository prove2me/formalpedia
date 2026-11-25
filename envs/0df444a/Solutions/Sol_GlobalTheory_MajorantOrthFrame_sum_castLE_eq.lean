-- Prove2me | solution 1 for GlobalTheory.MajorantOrthFrame.sum_castLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:06:38.693876+00:00
-- url     : https://prove2.me/submissions/0ccd893e-e018-42d4-adfb-8b8a13a3f069

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.MajorantOrthFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajorantOrthFrame
theorem _root_.solution {p r : ℕ} (h : p ≤ r) (f : Fin r → ℝ) :
    ∑ a : Fin p, f (Fin.castLE h a) = ∑ a : Fin r, if (a : ℕ) < p then f a else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE h a) ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro a _ b _ hab
    exact Fin.castLE_injective h hab
  · intro b hb
    exact ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl
end GlobalTheory.MajorantOrthFrame
