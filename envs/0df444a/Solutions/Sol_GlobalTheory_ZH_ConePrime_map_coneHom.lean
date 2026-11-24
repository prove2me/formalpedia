-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.map_coneHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:51.63127+00:00
-- url     : https://prove2.me/submissions/75de1ef3-6203-4c36-a108-0b647c48384d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
variable {k J A B : Type} [CommRing k] [CommRing A] [CommRing B]
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution (c : k →+* A) (r : J → A) (e : A →+* B) (f : MvPolynomial J k) :
    Polynomial.map e (coneHom c r f) = coneHom (e.comp c) (fun j => e (r j)) f := by
  have : (Polynomial.mapRingHom e).comp (coneHom c r) = coneHom (e.comp c) (fun j => e (r j)) := by
    apply MvPolynomial.ringHom_ext <;> simp [coneHom]
  exact RingHom.congr_fun this f
end GlobalTheory.ZH.ConePrime
