-- Prove2me | solution 1 for GlobalTheory.dehomogenise_ne_zero_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:11:06.875966+00:00
-- url     : https://prove2.me/submissions/28e26ed1-03db-4d5e-8e9b-e82048454e5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsAlgebraicIndependentRatiosOfGenericZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoordsNoHomogeneousRelationGenericHyperpla
import Theorems.Thm_GlobalTheory_aeval_eq_pow_mul_aeval_dehomogenise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K]
    {m : ℕ} {Q : MvPolynomial (Fin (m + 1)) K} {d : ℕ} (hQ : Q.IsHomogeneous d) (h0 : Q ≠ 0) :
    aeval (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) Q ≠ 0 := by
  intro h
  have hinj := IsFractionRing.injective (MvPolynomial (Fin (m + 1)) K)
    (FractionRing (MvPolynomial (Fin (m + 1)) K))
  have hx0 : (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘
      X) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    exact (map_ne_zero_iff _ hinj).mpr (X_ne_zero 0)
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := FractionRing (MvPolynomial (Fin (m + 1)) K)) hQ
    (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘ X) hx0
  rw [h, map_zero, mul_zero, aeval_algebraMap_apply, aeval_X_left_apply] at e
  exact h0 (hinj (by rw [e, map_zero]))
end GlobalTheory
