-- Prove2me | solution 1 for GlobalTheory.ModelRelProbe.j_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:21.219877+00:00
-- url     : https://prove2.me/submissions/3a24b009-4fa4-449a-ab06-7667ec42a948

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_DominatesLiftUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ModelRelProbe
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}
namespace GlobalTheory.ModelRelProbe
theorem _root_.solution {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  unfold Model.j
  rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
end GlobalTheory.ModelRelProbe
