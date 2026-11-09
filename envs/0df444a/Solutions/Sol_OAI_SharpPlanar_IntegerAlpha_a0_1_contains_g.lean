-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.a0_1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:35:21.263378+00:00
-- url     : https://prove2.me/submissions/975eec96-94d5-4d79-8c30-ee4401cff1ea

import Mathlib
import Definitions.Def_OAIQ098G080
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phase12_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phaseBase_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powBin_g

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
lemma phaseBox_contains (n : ℕ) : (phaseBox n).Contains (phase12 n) := by
  have hh := CBox.contains_powBin_g phaseBase_contains_g 4 (n%12) (by omega)
  rw [← phase12_eq_pow,phase12_mod_g] at hh
  exact hh

lemma spectralCoefficientBox_contains (n l : ℕ) :
    (spectralCoefficientBox n l).Contains (spectralCoefficient n l) := by
  have hh := CBox.contains_mul_g (coefficientBox_contains_g l) (phaseBox_contains (l*n))
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
    exact CBox.contains_add_g (ih (fun n hn => h n (by omega))) (h N (by omega))
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
lemma alphaBox_contains (n j : ℕ) : (alphaBox n j).Contains (basisAlpha n j) := by
  have hh (l : ℕ) : (if j<l then spectralCoefficientBox n l else zeroBox).Contains
      (if j<l then spectralCoefficient n l else 0) := by
    split_ifs <;> first | exact spectralCoefficientBox_contains n l | exact zeroBox_contains
  have hs := boxSum_contains 7 (fun l _ => hh l)
  rwa [sum_seven_Icc] at hs

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma a0_1_contains_g_oai : a0_1.Contains (basisAlpha 0 1) := by
  have he : alphaBox 0 1 = a0_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 1
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.a0_1_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.a0_1_contains_g_oai
