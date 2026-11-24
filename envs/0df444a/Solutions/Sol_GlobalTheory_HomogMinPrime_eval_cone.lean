-- Prove2me | solution 1 for GlobalTheory.HomogMinPrime.eval_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:04.080821+00:00
-- url     : https://prove2.me/submissions/0fd58a05-7d0e-43fb-99d5-3fcd6806e3ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KerConeMemMinimalPrimes
import Theorems.Thm_GlobalTheory_HomogMinPrime_eval_scale

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
    {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X) F
      = Polynomial.monomial e (eval₂Hom β u F) := by
  rw [eval_scale _ (fun a => Polynomial.C (u a)) Polynomial.X hF,
    ← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]
  congr 1
  exact (map_eval₂Hom β u (Polynomial.C : K →+* Polynomial K) F).symm
end GlobalTheory.HomogMinPrime
