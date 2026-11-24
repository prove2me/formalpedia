-- Prove2me | solution 1 for GlobalTheory.HomogMinPrime.mem_ker_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:39.532135+00:00
-- url     : https://prove2.me/submissions/39f81e2b-de56-42e0-a9e6-776c9b0ff0b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KerConeMemMinimalPrimes
import Theorems.Thm_GlobalTheory_HomogMinPrime_eval_cone

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
theorem _root_.solution {o σ K : Type} [CommRing o] [Field K] (β : o →+* K) (u : σ → K)
    (F : MvPolynomial σ o) :
    F ∈ RingHom.ker (eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X)) ↔
      ∀ e, eval₂Hom β u (homogeneousComponent e F) = 0 := by
  rw [RingHom.mem_ker]
  have h : eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X) F =
      ∑ e ∈ Finset.range (F.totalDegree + 1),
        Polynomial.monomial e (eval₂Hom β u (homogeneousComponent e F)) := by
    conv_lhs => rw [← sum_homogeneousComponent F, map_sum]
    exact Finset.sum_congr rfl fun e _ => eval_cone β u (homogeneousComponent_isHomogeneous e F)
  rw [h]
  constructor
  · intro h0 e
    by_cases he : e ∈ Finset.range (F.totalDegree + 1)
    · have := congrArg (fun p => Polynomial.coeff p e) h0
      simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero,
        Finset.sum_ite_eq', he, if_true] at this
      exact this
    · rw [homogeneousComponent_eq_zero, map_zero]
      rw [Finset.mem_range] at he
      omega
  · intro h0
    exact Finset.sum_eq_zero fun e _ => by rw [h0, map_zero]
end GlobalTheory.HomogMinPrime
