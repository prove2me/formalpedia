-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.ext_valF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:55:08.910717+00:00
-- url     : https://prove2.me/submissions/0030661b-5186-45e2-9fcb-6bcc77a04c59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldRestrictionTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.FieldRestrictionTest
theorem _root_.solution {g g' : GtPtF D F} (hb : g.b = g'.b)
    (hs : ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = val (g'.s χ) (𝟙 _) y J) : g = g' := by
  obtain ⟨b, s, h, _, _⟩ := g
  obtain ⟨b', s', h', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ =>
    GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ) (corr_of_val D.P.isLB (hs χ))
  rfl
end GlobalTheory.FieldRestrictionTest
