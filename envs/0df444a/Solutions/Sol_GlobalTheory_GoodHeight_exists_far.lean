-- Prove2me | solution 1 for GlobalTheory.GoodHeight.exists_far
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:36:37.217154+00:00
-- url     : https://prove2.me/submissions/0f90b6d5-8c57-4062-b6c9-5e346127efcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GoodHeight
namespace GlobalTheory.GoodHeight
theorem _root_.solution (S : Finset ℝ) (T : ℝ) : ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
    ∀ x ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |x - T'| := by
  classical
  by_contra hcon
  push Not at hcon
  have hn : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have key : ∀ k ∈ Finset.range (S.card + 1), ∃ x ∈ S,
      |x - (T + (k : ℝ) / ((S.card : ℝ) + 1))| < 1 / (2 * ((S.card : ℝ) + 1)) := by
    intro k hk
    have hk' : (k : ℝ) ≤ S.card := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    apply hcon
    · have : 0 ≤ (k : ℝ) / ((S.card : ℝ) + 1) := by positivity
      linarith
    · have : (k : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hn]; linarith
      linarith
  choose! g hgS hg using key
  obtain ⟨a, ha, b, hb, hab, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (S.card + 1)) (t := S)
      (by simp) (fun k hk => hgS k hk)
  have h1 := hg a ha
  have h2 := hg b hb
  rw [heq] at h1
  have hclose : |(a : ℝ) / ((S.card : ℝ) + 1) - (b : ℝ) / ((S.card : ℝ) + 1)|
      < 1 / ((S.card : ℝ) + 1) := by
    calc |(a : ℝ) / ((S.card : ℝ) + 1) - (b : ℝ) / ((S.card : ℝ) + 1)|
        = |(g b - (T + (b : ℝ) / ((S.card : ℝ) + 1))) - (g b - (T + (a : ℝ) / ((S.card : ℝ) + 1)))| := by
          congr 1; ring
      _ ≤ |g b - (T + (b : ℝ) / ((S.card : ℝ) + 1))| + |g b - (T + (a : ℝ) / ((S.card : ℝ) + 1))| :=
          abs_sub _ _
      _ < 1 / (2 * ((S.card : ℝ) + 1)) + 1 / (2 * ((S.card : ℝ) + 1)) := add_lt_add h2 h1
      _ = 1 / ((S.card : ℝ) + 1) := by field_simp; ring
  rw [← sub_div, abs_div, abs_of_pos hn, div_lt_div_iff_of_pos_right hn] at hclose
  have hsep : (1 : ℝ) ≤ |(a : ℝ) - b| := by
    rcases lt_or_gt_of_ne hab with h | h
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  linarith
end GlobalTheory.GoodHeight
