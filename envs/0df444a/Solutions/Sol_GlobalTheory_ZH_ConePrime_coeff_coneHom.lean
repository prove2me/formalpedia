-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.coeff_coneHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:25:29.204662+00:00
-- url     : https://prove2.me/submissions/9f4b5d79-4bf0-4abb-88f8-d2a07c362219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Theorems.Thm_GlobalTheory_ZH_ConePrime_coneHom_of_isHomogeneous

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
theorem _root_.solution (c : k →+* A) (r : J → A) (f : MvPolynomial J k) (n : ℕ) :
    (coneHom c r f).coeff n = MvPolynomial.eval₂Hom c r (MvPolynomial.homogeneousComponent n f) := by
  conv_lhs => rw [← f.sum_homogeneousComponent]
  rw [map_sum, Polynomial.finset_sum_coeff]
  simp only [coneHom_of_isHomogeneous c r (MvPolynomial.homogeneousComponent_isHomogeneous _ f),
    Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by simpa using h), map_zero]
end GlobalTheory.ZH.ConePrime
