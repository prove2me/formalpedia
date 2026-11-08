-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_exact_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:22:57.507004+00:00
-- url     : https://prove2.me/submissions/e88d155b-7141-4a93-8c78-a8db646b211f

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_fejerPolynomial_degree_g
import Theorems.Thm_OAI_SharpPlanar_fejerPolynomial_eval_g
import Theorems.Thm_OAI_SharpPlanar_fejer_polynomial_integral_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma fejer_exact_g_oai (P : ℝ[X]) (hP : P.degree < 256) :
    ∑ v ∈ Finset.range 256, fejerWeight v * P.eval (fejerNode v) =
      (1/2:ℝ)*(∫ x in (-1:ℝ)..1, P.eval x) := by
  by_cases hp : P=0
  · simp [hp]
  have hdP : P.natDegree ≤ 255 := by
    have : P.natDegree < (256:ℕ) := (natDegree_lt_iff_degree_lt hp).mpr hP
    omega
  have hdF : fejerPolynomial.natDegree ≤ 254 :=
    natDegree_le_iff_degree_le.mpr fejerPolynomial_degree_g
  have hd : (fejerPolynomial*P).degree < 2*256 := by
    apply lt_of_le_of_lt (degree_le_natDegree)
    have hnat : (fejerPolynomial*P).natDegree ≤ 509 :=
      (natDegree_mul_le).trans (by omega)
    exact_mod_cast (by omega : (fejerPolynomial*P).natDegree < 2*256)
  have h := integral_eq_sumZeroes (P:=fejerPolynomial*P) (by norm_num : 256 ≠ 0) hd
  simp only [eval_mul] at h
  rw [fejer_polynomial_integral_g P hP] at h
  unfold sumZeroes at h
  have he : ∀ v : ℕ, Real.cos (((2*(v:ℝ)+1)/512)*Real.pi) = fejerNode v := by
    intro v
    unfold fejerNode fejerAngle
    congr 1
    ring
  norm_num only [Nat.cast_ofNat] at h
  simp only [he, eval_mul, fejerPolynomial_eval_g] at h
  simp only [mul_assoc, ← Finset.mul_sum] at h
  have halg (A B : ℝ) (hab : Real.pi/2*A = Real.pi/256*(256*B)) :
      B=(1/2:ℝ)*A := by nlinarith only [hab, Real.pi_pos]
  exact halg _ _ h

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_exact_g_oai := @OAI.SharpPlanar.fejer_exact_g_oai
