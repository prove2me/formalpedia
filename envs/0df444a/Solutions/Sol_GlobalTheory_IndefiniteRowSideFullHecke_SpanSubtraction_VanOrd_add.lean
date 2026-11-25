-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.VanOrd.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:05.008968+00:00
-- url     : https://prove2.me/submissions/1b15668b-93a2-400a-9c5b-9842e14d15f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_SpanSubtraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology Asymptotics
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
namespace VanOrd
theorem _root_.solution {X : Data E r} {Xa : ArchInM X} {Fl : FlatM X Xa} {a : ℕ}
    {f g : Frame X.Ψ r → ℂ} (hf : VanOrd Fl a f) (hg : VanOrd Fl a g) :
    VanOrd Fl a fun x => f x + g x := fun j => (hf j).add (hg j)
end VanOrd
end GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
