-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.formEq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:49:06.502943+00:00
-- url     : https://prove2.me/submissions/f6de0ffb-a8b6-44b4-816f-35a6dc94973b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff

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
theorem _root_.solution (χ : D.X) : FormEq (K' := PEmpty) (DegPre.gtφT D T (DegPre.zeroT D T) χ) DegPre.gtε
    PEmpty.elim PEmpty.elim := fun U _ h => by
  rw [Fin.prod_univ_four]
  show h (cP D T χ * 1).left ^ (-1 : ℤ) * h (cP D T χ).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  rw [_root_.mul_one]; simp
end GlobalTheory.FieldRestrictionTest
