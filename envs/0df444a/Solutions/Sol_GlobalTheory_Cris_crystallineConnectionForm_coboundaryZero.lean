-- Prove2me | solution 1 for GlobalTheory.Cris.crystallineConnectionForm_coboundaryZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:31.49675+00:00
-- url     : https://prove2.me/submissions/c633c8b2-7db0-47e6-8eaa-16a073f19382

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
open KaehlerDifferential
variable (R) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
attribute [local instance] opModule
attribute [local instance] isCentralScalar_kaehler isScalarTower_kaehler
variable {R B B'} {s : X ⟶ Sp R}
namespace GlobalTheory.Cris
theorem _root_.solution (g : C0 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    connForm ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩ x hx = D R B (g (Thick.triv B x hx)) := by
  change TrivSqZeroExt.snd (R := B) ((_ - TrivSqZeroExt.inl _) - (_ - diagSec R B _)) = _
  simp
end GlobalTheory.Cris
