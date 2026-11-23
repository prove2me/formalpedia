-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.coneHom_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:27.738858+00:00
-- url     : https://prove2.me/submissions/87dde029-0f70-4698-80b7-f754d09ceb00

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
theorem _root_.solution (c : k →+* A) (r : J → A) {f : MvPolynomial J k} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    coneHom c r f = Polynomial.monomial n (MvPolynomial.eval₂Hom c r f) := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hn : d.sum (fun _ e => e) = n := by
    have := hf (MvPolynomial.mem_support_iff.1 hd)
    rw [← this, Finsupp.weight_apply]
    simp
  rw [← hn, ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [coneHom, MvPolynomial.eval₂Hom_monomial, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, RingHom.comp_apply, _root_.mul_assoc]
end GlobalTheory.ZH.ConePrime
