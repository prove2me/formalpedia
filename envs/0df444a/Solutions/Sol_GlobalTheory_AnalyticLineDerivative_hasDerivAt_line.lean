-- Prove2me | solution 1 for GlobalTheory.AnalyticLineDerivative.hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:47.379718+00:00
-- url     : https://prove2.me/submissions/b8a8424b-d327-4edd-8193-1d3bcd714d7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticLineDerivative
open MvPolynomial
universe u_1 u_2 u_3 u_4
namespace GlobalTheory.AnalyticLineDerivative
theorem _root_.solution {S : Type*} {J : Type*} [CommRing S] [Fintype J] (φ : S →+* ℂ)
    (u v : J → ℂ) (p : MvPolynomial J S) :
    HasDerivAt (fun t : ℂ => eval₂Hom φ (u + t • v) p)
      (∑ j, v j * eval₂Hom φ u (pderiv j p)) 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval₂Hom_C, pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    have hlin : HasDerivAt (fun t : ℂ => u i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (u i)
    have hX : ∀ j, eval₂Hom φ u (pderiv j (X i : MvPolynomial J S)) = if j = i then 1 else 0 := by
      intro j
      by_cases h : j = i
      · subst h; simp [pderiv_X]
      · simp [pderiv_X, h, Ne.symm h]

    have key : ∀ j, v j * eval₂Hom φ u (pderiv j (p * X i)) =
        (if j = i then v i * eval₂Hom φ u p else 0) + v j * eval₂Hom φ u (pderiv j p) * u i := by
      intro j
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, eval₂Hom_X', hX]
      split_ifs with h
      · subst h; ring
      · ring
    simp only [map_mul, eval₂Hom_X', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (hp.mul hlin).congr_deriv ?_
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_smul,
      add_zero, zero_mul]
    ring
end GlobalTheory.AnalyticLineDerivative
