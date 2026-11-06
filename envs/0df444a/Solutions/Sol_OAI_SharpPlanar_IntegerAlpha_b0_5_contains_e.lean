-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b0_5_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T02:13:50.427639+00:00
-- url     : https://prove2.me/submissions/4da73dce-c446-4f4a-8004-55e1e61fdaad

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phaseBase_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powBin_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phase12_eq_pow (n : ℕ) : phase12 n = phase12 1^n := by
  rw [phase12,phase12,← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
lemma phase12_periodic (n : ℕ) : phase12 (n+12) = phase12 n := by
  unfold phase12
  have he : Complex.I*Real.pi*(((n+12:ℕ):ℂ)/6) =
      Complex.I*Real.pi*((n:ℂ)/6)+2*Real.pi*Complex.I := by push_cast <;> ring
  rw [he,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
lemma phase12_mod (n : ℕ) : phase12 (n%12) = phase12 n :=
  (show Function.Periodic phase12 12 from phase12_periodic).map_mod_nat n

lemma phaseBox_contains (n : ℕ) : (phaseBox n).Contains (phase12 n) := by
  have hh := CBox.contains_powBin_e phaseBase_contains_e 4 (n%12) (by omega)
  rw [← phase12_eq_pow,phase12_mod] at hh
  exact hh

lemma spectralCoefficientBox_contains (n l : ℕ) :
    (spectralCoefficientBox n l).Contains (spectralCoefficient n l) := by
  have hh := CBox.contains_mul_e (coefficientBox_contains_e l) (phaseBox_contains (l*n))
  unfold spectralCoefficientBox
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerIntervals

lemma zeroBox_contains : zeroBox.Contains 0 := by simp [zeroBox,CBox.Contains,RBox.Contains]
lemma boxSum_contains {f : ℕ → CBox} {g : ℕ → ℂ} (N : ℕ)
    (h : ∀ n < N, (f n).Contains (g n)) :
    (boxSum f N).Contains (∑ n ∈ Finset.range N, g n) := by
  induction N with
  | zero => simpa [boxSum] using zeroBox_contains
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact CBox.contains_add_e (ih (fun n hn => h n (by omega))) (h N (by omega))
end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma sum_seven_Icc (f : ℕ → ℂ) (j : ℕ) :
    (∑ l ∈ Finset.range 7, if j<l then f l else 0) = ∑ l ∈ Finset.Icc (j+1) 6, f l := by
  rw [← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
  omega
lemma betaBox_contains (n j : ℕ) : (betaBox n j).Contains (basisBeta n j) := by
  have hh (l : ℕ) : (if j<l then (spectralCoefficientBox n l).scale l 6 else zeroBox).Contains
      (if j<l then ((l:ℂ)/6)*spectralCoefficient n l else 0) := by
    split_ifs
    · simpa only [Int.cast_natCast,Int.cast_ofNat] using CBox.contains_scale_e (spectralCoefficientBox_contains n l) l 6 (by norm_num)
    · exact zeroBox_contains
  have hs := boxSum_contains 7 (fun l _ => hh l)
  rwa [sum_seven_Icc] at hs

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma b0_5_contains_e_oai : b0_5.Contains (basisBeta 0 5) := by
  have he : betaBox 0 5 = b0_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 5
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b0_5_contains_e_oai := @OAI.SharpPlanar.IntegerAlpha.b0_5_contains_e_oai
