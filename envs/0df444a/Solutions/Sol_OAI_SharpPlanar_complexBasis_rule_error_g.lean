-- Prove2me | solution 1 for OAI.SharpPlanar.complexBasis_rule_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:30:45.173591+00:00
-- url     : https://prove2.me/submissions/b85e87a8-e4e4-47ff-8101-fe132df0d550

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_rule_error_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory

lemma singleCoefficient_mass {n : ℕ} (hn : n ≤ 100) :
    ∑ k ∈ Finset.range 101, |singleCoefficient n k| = 1 := by
  simp [singleCoefficient, apply_ite, show n < 101 by omega]
lemma singleDensity_u {n : ℕ} (hn : n ≤ 100) (j : ℕ) (t : ℂ) :
    finiteDensity (singleCoefficient n) (fun _ => 0) j t = complexU n j t := by
  simp [finiteDensity,singleCoefficient,apply_ite,ite_mul,show n < 101 by omega]
lemma singleDensity_v {n : ℕ} (hn : n ≤ 100) (j : ℕ) (t : ℂ) :
    finiteDensity (fun _ => 0) (singleCoefficient n) j t = complexV n j t := by
  simp [finiteDensity,singleCoefficient,apply_ite,ite_mul,show n < 101 by omega]

lemma complexBasis_rule_error_g_oai {n m : ℕ} (hn : n ≤ 100) (hm : m ≤ 100) (d e : Bool) :
    ‖(∑ j : Fin 6, pieceIntegral (complexBasisMoment d e n j.val m) j.val)-
      ∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val‖ < 1/10^22 := by
  have hw1 : ∑ k ∈ Finset.range 101, (|singleCoefficient n k|+|(0:ℝ)|) ≤ 3 := by
    simp only [abs_zero,add_zero,singleCoefficient_mass hn] <;> norm_num
  have hw2 : ∑ k ∈ Finset.range 101, (|(0:ℝ)|+|singleCoefficient n k|) ≤ 3 := by
    simp only [abs_zero,zero_add,singleCoefficient_mass hn] <;> norm_num
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hm1 : (m:ℝ) ≤ 100 := by exact_mod_cast hm
  unfold complexBasisMoment complexBasis
  cases d
  · simpa only [singleDensity_u hn,Bool.false_eq_true,ite_false, if_false]
      using transformedMoment_rule_error_g (singleCoefficient n) (fun _ => 0) hw1
        hm0 hm1 (y := 1) (by norm_num) (if e then 1 else 0)
  · simpa only [singleDensity_v hn,ite_true, if_true]
      using transformedMoment_rule_error_g (fun _ => 0) (singleCoefficient n) hw2
        hm0 hm1 (y := 1) (by norm_num) (if e then 1 else 0)

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexBasis_rule_error_g_oai := @OAI.SharpPlanar.complexBasis_rule_error_g_oai
