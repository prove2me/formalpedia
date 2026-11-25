-- Prove2me | solution 1 for GlobalTheory.PoincareAssembly.poin_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:33.654873+00:00
-- url     : https://prove2.me/submissions/5cbdfbe2-f49c-4cc7-b134-0e90180077cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PoinStatementOf
import Theorems.Thm_GlobalTheory_PoincareAssembly_norm_chi

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
open GlobalTheory GlobalTheory.PoincareAssembly
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PoincareAssembly
theorem _root_.solution {r : ℕ} (X : Data E r) (la la' : Wt X.Ψ r) (P g : Frame X.Ψ r → ℂ)
    (hg : X.IsSec la' g) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  have h1 : X.χ la' γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la' γ.2]; exact one_ne_zero
  have h2 : X.χ la γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la γ.2]; exact one_ne_zero
  simp only [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]
  field_simp
end GlobalTheory.PoincareAssembly
