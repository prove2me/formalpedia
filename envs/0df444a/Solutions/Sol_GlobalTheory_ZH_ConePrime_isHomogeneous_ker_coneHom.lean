-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.isHomogeneous_ker_coneHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:54.746894+00:00
-- url     : https://prove2.me/submissions/6c280a35-03fd-4d36-a96d-8a9c63787f49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Theorems.Thm_GlobalTheory_ZH_ConePrime_coneHom_of_isHomogeneous
import Theorems.Thm_GlobalTheory_ZH_ConePrime_coeff_coneHom

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
theorem _root_.solution (c : k →+* A) (r : J → A) :
    (RingHom.ker (coneHom c r)).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) := by
  intro n f hf
  rw [RingHom.mem_ker] at hf
  have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule J k) f n : MvPolynomial.homogeneousSubmodule J k n) : MvPolynomial J k) = MvPolynomial.homogeneousComponent n f :=
    MvPolynomial.decomposition.decompose'_apply f n
  rw [e]
  rw [RingHom.mem_ker, coneHom_of_isHomogeneous c r (MvPolynomial.homogeneousComponent_isHomogeneous _ f),
    ← coeff_coneHom, hf]
  simp
end GlobalTheory.ZH.ConePrime
