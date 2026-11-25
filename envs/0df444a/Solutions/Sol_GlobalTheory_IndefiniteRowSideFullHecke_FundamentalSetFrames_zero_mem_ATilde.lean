-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.zero_mem_ATilde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:52:07.476617+00:00
-- url     : https://prove2.me/submissions/cae78738-8d9c-4b1f-be6b-e42de135908f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FundamentalSetFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open scoped ENNReal NNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
theorem _root_.solution (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (la : Wt X.Ψ r)
    (u : Frame X.Ψ r → EReal) : (fun _ => 0) ∈ ATilde X x0 bb la u :=
  ⟨differentiableOn_const 0, by simp [normSq, wsq]⟩
end GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
