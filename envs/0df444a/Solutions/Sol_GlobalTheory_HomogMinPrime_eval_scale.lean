-- Prove2me | solution 1 for GlobalTheory.HomogMinPrime.eval_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:20.813624+00:00
-- url     : https://prove2.me/submissions/217132ba-b990-4b82-8e72-d8d12f81f34f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KerConeMemMinimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.HomogMinPrime
open MvPolynomial
namespace GlobalTheory.HomogMinPrime
theorem _root_.solution {o σ A : Type} [CommRing o] [CommRing A] (f : o →+* A) (g : σ → A) (c : A)
    {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    eval₂Hom f (fun a => g a * c) F = c ^ e * eval₂Hom f g F := by
  classical
  rw [F.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = e := by
    by_contra h
    exact (mem_support_iff.mp hd) (hF.coeff_eq_zero h)
  rw [eval₂Hom_monomial, eval₂Hom_monomial, ← hdeg]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree_apply]
  ring
end GlobalTheory.HomogMinPrime
