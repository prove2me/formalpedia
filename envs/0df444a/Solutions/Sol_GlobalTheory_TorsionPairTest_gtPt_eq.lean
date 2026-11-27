-- Prove2me | solution 1 for GlobalTheory.TorsionPairTest.gtPt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:00.744818+00:00
-- url     : https://prove2.me/submissions/ca451e2b-d21c-4bf5-9fce-d425085d6817

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_EquivIffOfIsEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionPairTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
variable {T : Over (Spec (CommRingCat.of R))} [IsEmpty T.left]
namespace GlobalTheory.TorsionPairTest
theorem _root_.solution (g g' : GtPt D T) : g = g' := by
  obtain ⟨b, s, _, _, _⟩ := g
  obtain ⟨b', s', _, _, _⟩ := g'
  obtain rfl : b = b' := hom_eq _ _
  obtain rfl : s = s' := funext fun χ => by
    have : (s χ).s = (s' χ).s := funext fun _ => Units.ext (Subsingleton.elim _ _)
    cases h : s χ; cases h' : s' χ
    rw [h, h'] at this
    congr
  rfl
end GlobalTheory.TorsionPairTest
