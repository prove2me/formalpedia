-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:20:17.053289+00:00
-- url     : https://prove2.me/submissions/7d52b50e-aa99-40ef-8c1e-3d545bde36f0

import Mathlib
import Definitions.Def_Q238K011
import Definitions.Def_Q238K014
import Theorems.Thm_OAI_MetricKMedianRecovery_Categorical_Selected_binaryGreedyOutput_expected_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ average X :=
  Finset.expect_nonneg (fun ω _ => h ω)

end Average

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Explicit
open FiniteSampling

lemma steps_pos (a : ℕ) : 0 < steps a := pow_pos (by decide) _
lemma steps_lower (a : ℕ) : 1000*(a+1)^2 ≤ steps a := by
  have hh : a+1 ≤ 2^(a+1).size := (Nat.lt_size_self _).le
  have hs := Nat.pow_le_pow_left hh 2
  unfold steps exponent
  rw [pow_add,show 2*(a+1).size=(a+1).size*2 by omega,pow_mul]
  norm_num
  nlinarith
lemma samples_pos (q a : ℕ) : 0 < samples q a := by unfold samples; have := steps_pos a; positivity
lemma scale (a : ℕ) : (a:ℝ)^2 ≤ (1/1000:ℝ)*steps a := by
  have hh : (1000:ℝ)*(a+1)^2 ≤ steps a := by exact_mod_cast steps_lower a
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith
attribute [local irreducible] steps exponent
lemma count (q a : ℕ) : ((steps a:ℕ):ℝ)*q*a^2/(4*(1/1000:ℝ)^3) ≤ samples q a := by
  unfold samples
  push_cast
  have ht : (0:ℝ) ≤ steps a := Nat.cast_nonneg _
  have hq : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg _
  have hsq : (a:ℝ)^2 ≤ (a+1)^2 := by nlinarith
  have hh : (steps a:ℝ)*q*a^2 ≤ steps a*(q+1)*(a+1)^2 := by gcongr; linarith
  calc
    _ = 250000000*((steps a:ℝ)*q*a^2) := by ring
    _ ≤ 250000000*(steps a*(q+1)*(a+1)^2) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ _ := by
      have hn : (0:ℝ) ≤ steps a*(q+1)*(a+1)^2 := by positivity
      nlinarith

attribute [local irreducible] samples
end MetricKMedianRecovery.Categorical.Explicit

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchChecksCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm
open Categorical.Explicit
open MetricKMedianRecovery.Categorical
variable {q a p r : ℕ}
attribute [local irreducible] BinaryCategorical.rule exponent samples
lemma sixtyTwoFin_s238_oai (part : Fin q→Fin a) (rule : Selected.Rule part) (g : SetFunction (Fin q))
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅=0)
    (X : Finset (Fin q)) (hX : PartitionFeasible part X) :
    (62/100:ℝ)*g X ≤ FiniteSampling.average
      (fun bits : BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool =>
        g (Selected.binaryGreedyOutput part rule g bits)) := by
  by_cases ha : 0<a
  · have hh:=Selected.binaryGreedyOutput_expected_s238 (b:=exponent a) (L:=samples q a) part rule g hmono hsub hg0 ha
      (show (0:ℝ)<1/1000 by norm_num) (by norm_num) (by simpa only [steps] using scale a)
      (samples_pos q a) (by simpa only [steps,Fintype.card_fin] using count q a) X hX
    have he : 1/Real.exp 1 ≤ (37/100:ℝ) := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      linarith [Real.exp_one_gt_d9]
    have hn : 0 ≤ g X := by rw [←hg0]; exact hmono (Finset.empty_subset _)
    exact (mul_le_mul_of_nonneg_right (by linarith : (62/100:ℝ) ≤ 1-1/Real.exp 1-4*(1/1000)) hn).trans hh
  · have hE : IsEmpty (Fin q) := ⟨fun e=>by have := (part e).isLt; omega⟩
    have hX0 : X=∅ := Subsingleton.elim _ _
    rw [hX0,hg0,mul_zero]
    apply FiniteSampling.average_nonneg
    intro bits
    rw [Subsingleton.elim (Selected.binaryGreedyOutput part rule g bits) ∅,hg0]

end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238_oai
