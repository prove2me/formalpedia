-- Prove2me | solution 1 for GlobalTheory.TorsionZero.aeval_cone_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:32:56.367633+00:00
-- url     : https://prove2.me/submissions/c081ea54-9cac-43f5-9127-78536b4ea2d1

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
import Theorems.Thm_GlobalTheory_TorsionZero_aeval_mul_of_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K σ : Type} [Field K]
namespace GlobalTheory.TorsionZero
theorem _root_.solution {C : Type} [CommRing C] [Algebra K C] (r : σ → C)
    (G : MvPolynomial σ K) :
    aeval (fun j => Polynomial.C (r j) * Polynomial.X) G = 0 ↔
      ∀ n, aeval r (homogeneousComponent n G) = 0 := by
  have hm : ∀ n, aeval (fun j => Polynomial.C (r j) * Polynomial.X) (homogeneousComponent n G) =
      Polynomial.C (aeval r (homogeneousComponent n G)) * Polynomial.X ^ n := fun n => by
    rw [aeval_mul_of_isHomogeneous _ _ (homogeneousComponent_isHomogeneous n G)]
    congr 1
    exact (comp_aeval_apply r (Polynomial.CAlgHom (R := K) (A := C)) _).symm
  constructor
  · intro h n
    by_cases hn : n ∈ Finset.range (G.totalDegree + 1)
    · rw [← sum_homogeneousComponent G, map_sum] at h
      have h2 := congrArg (fun p => Polynomial.coeff p n) h
      simp only [Polynomial.finset_sum_coeff, hm, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h2
      rw [Finset.sum_eq_single n] at h2
      · simpa using h2
      · intro b _ hb
        rw [if_neg (Ne.symm hb)]
      · exact fun h' => absurd hn h'
    · rw [homogeneousComponent_eq_zero _ _ (by simpa using hn), map_zero]
  · intro h
    rw [← sum_homogeneousComponent G, map_sum]
    exact Finset.sum_eq_zero fun n _ => by rw [hm, h, map_zero, zero_mul]
end GlobalTheory.TorsionZero
