-- Prove2me | solution 1 for GlobalTheory.LatFin.finite_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:35.748243+00:00
-- url     : https://prove2.me/submissions/5bdfd077-eb37-43c9-81d2-62e43c675b89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Theorems.Thm_GlobalTheory_LatFin_finite_bounded
import Theorems.Thm_GlobalTheory_LatFin_exists_common_den

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
open GlobalTheory GlobalTheory.LatFin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LatFin
theorem _root_.solution (r : ℕ) (X : Data E r) (R : ℝ) :
    {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  refine (Set.Finite.pi' fun _ : Fin r => finite_bounded X.Ψ X.cmType k hk R).subset ?_
  rintro v ⟨hv, hb⟩ a
  exact ⟨hi v hv a, fun τ => hb τ a⟩
end GlobalTheory.LatFin
