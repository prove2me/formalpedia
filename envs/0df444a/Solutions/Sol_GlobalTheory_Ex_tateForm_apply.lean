-- Prove2me | solution 1 for GlobalTheory.Ex.tateForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:47.304626+00:00
-- url     : https://prove2.me/submissions/8b5690b5-673f-427d-9230-a7ad05332048

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
namespace GlobalTheory.Ex
theorem _root_.solution {C : Type} [NormedField C] (q : Cˣ) (n : ℤ) :
    tateForm q n = (n : ℝ) ^ 2 * (-Real.log ‖(q : C)‖) := by
  simp [tateForm, sq]
end GlobalTheory.Ex
