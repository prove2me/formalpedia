-- Prove2me | solution 1 for OAI.BufferedIsing.DSS.interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:54:20.354271+00:00
-- url     : https://prove2.me/submissions/4a84b8f6-cea1-4270-8913-78fcaf1cc9f1

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Interpolation.lean:L97-L147
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.DSS.interpolation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation

-- ---- from OAI.Probability.Ising.Interpolation ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

lemma update_den_pos {a c : ℝ} (ha : -1 < a ∧ a < 1)
    (hc : -1 < c ∧ c < 1) : 0 < 1 + a * c := by
  have h := abs_mul a c
  have haa : |a| < 1 := abs_lt.mpr ha
  have hcc : |c| < 1 := abs_lt.mpr hc
  have hh : |a * c| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg a, abs_nonneg c]
  have := (abs_lt.mp hh).1
  linarith

lemma interpolation_positive_sum {a b c : ℝ}
    (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1)
    (hab : b ≤ a) (hc : 0 ≤ c ∧ c < 1) (hs : 0 ≤ a + b) :
    ∃ d : ℝ, -1 < d ∧ d < 1 ∧
      (1 - a) * (1 - d) / (1 + a * d) ≤
        (1 + (a - b) * c / 2) * (1 - a) / (1 + a * c) ∧
      (1 + b) * (1 + d) / (1 + b * d) ≤
        (1 + (a - b) * c / 2) * (1 + b) / (1 - b * c) := by
  have ha0 : 0 ≤ a := by linarith
  let k := 1 + (a - b) * c / 2
  let A := 1 + a * c
  have hk : 0 < k := by dsimp [k]; nlinarith [mul_nonneg (sub_nonneg.mpr hab) hc.1]
  have hA : 0 < A := by dsimp [A]; nlinarith [mul_nonneg ha0 hc.1]
  have hD : 0 < A + a * k := by positivity
  let d := (A - k) / (A + a * k)
  have hN : 0 ≤ A - k := by dsimp [A, k]; nlinarith [mul_nonneg hs hc.1]
  have hd0 : 0 ≤ d := div_nonneg hN hD.le
  have hd1 : d < 1 := by
    apply (div_lt_one hD).mpr
    nlinarith [mul_pos hk (by linarith : 0 < 1 + a)]
  have hda : 0 < 1 + a * d := update_den_pos ha ⟨by linarith, hd1⟩
  have hdb : 0 < 1 + b * d := update_den_pos hb ⟨by linarith, hd1⟩
  have hbC : 0 < 1 - b * c := by
    have := update_den_pos hb (a := b) (c := -c) (by constructor <;> linarith)
    nlinarith
  have heq : A * (1 - d) = k * (1 + a * d) := by
    dsimp [d]
    field_simp
    ring
  refine ⟨d, by linarith, hd1, ?_, ?_⟩
  · apply (div_le_div_iff₀ hda hA).mpr
    change (1 - a) * (1 - d) * A ≤ k * (1 - a) * (1 + a * d)
    nlinarith [heq]
  · have hsums : (1 + a * d) * (1 + d) + (1 + b * d) * (1 - d) ≥
        2 * (1 - d) * (1 + d) := by
      nlinarith [mul_nonneg hs hd0,
        mul_nonneg (show 0 ≤ 2 + a - b by linarith) (sq_nonneg d)]
    have ht : (1 - b * c) * (1 + d) ≤ k * (1 + b * d) := by
      have hkA : A + (1 - b * c) = 2 * k := by dsimp [A,k]; ring
      have hh := mul_nonneg hk.le (sub_nonneg.mpr hsums)
      nlinarith [heq]
    apply (div_le_div_iff₀ hdb hbC).mpr
    change (1 + b) * (1 + d) * (1 - b * c) ≤ k * (1 + b) * (1 + b * d)
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + b) (sub_nonneg.mpr ht)]

lemma interpolation_pair {a b c : ℝ}
    (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1)
    (hab : b ≤ a) (hc : 0 ≤ c ∧ c < 1) :
    ∃ d : ℝ, -1 < d ∧ d < 1 ∧
      (1 - a) * (1 - d) / (1 + a * d) ≤
        (1 + (a - b) * c / 2) * (1 - a) / (1 + a * c) ∧
      (1 + b) * (1 + d) / (1 + b * d) ≤
        (1 + (a - b) * c / 2) * (1 + b) / (1 - b * c) := by
  by_cases hs : 0 ≤ a + b
  · exact interpolation_positive_sum ha hb hab hc hs
  · obtain ⟨e, he0, he1, h1, h2⟩ := interpolation_positive_sum
      (a := -b) (b := -a) (by constructor <;> linarith)
      (by constructor <;> linarith) (by linarith) hc (by linarith)
    refine ⟨-e, by linarith, by linarith, ?_, ?_⟩
    · convert h2 using 1 <;> congr 1 <;> ring
    · convert h1 using 1 <;> congr 1 <;> ring

lemma one_sub_update {a c : ℝ} (hd : 1 + a * c ≠ 0) :
    1 - update a c = (1 - a) * (1 - c) / (1 + a * c) := by
  dsimp [update]
  field_simp
  ring

lemma one_add_update {a c : ℝ} (hd : 1 + a * c ≠ 0) :
    1 + update a c = (1 + a) * (1 + c) / (1 + a * c) := by
  dsimp [update]
  field_simp
  ring

/-- Finite-field interpolation with a common finite field parameter for both one-sided mixtures. -/
theorem interpolation {a b c z : ℝ}
    (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1)
    (hab : b ≤ a) (hc : 0 ≤ c ∧ c < 1)
    (hz : 0 ≤ z) (hgap : a - b ≤ 2 * z) :
    ∃ d : ℝ, -1 < d ∧ d < 1 ∧
      update a c ≤ ((1 - c) / (1 + z * c)) * update a d +
        (1 - (1 - c) / (1 + z * c)) ∧
      ((1 - c) / (1 + z * c)) * update b d -
        (1 - (1 - c) / (1 + z * c)) ≤ update b (-c) := by
  obtain ⟨d, hd0, hd1, h1, h2⟩ := interpolation_pair ha hb hab hc
  let α := (1 - c) / (1 + z * c)
  let k := 1 + (a - b) * c / 2
  have hc' : -1 < c ∧ c < 1 := ⟨by linarith, hc.2⟩
  have hmc : -1 < -c ∧ -c < 1 := by constructor <;> linarith
  have hK : 0 < 1 + z * c := by nlinarith [mul_nonneg hz hc.1]
  have hα : 0 ≤ α := div_nonneg (by linarith) hK.le
  have hk : k ≤ 1 + z * c := by
    dsimp [k]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgap) hc.1]
  have hαk : α * k ≤ 1 - c := by
    calc
      α * k ≤ α * (1 + z * c) := mul_le_mul_of_nonneg_left hk hα
      _ = 1 - c := by exact div_mul_cancel₀ _ hK.ne'
  have hDa : 0 ≤ (1 - a) / (1 + a * c) :=
    div_nonneg (by linarith) (update_den_pos ha hc').le
  have hDb : 0 ≤ (1 + b) / (1 - b * c) := by
    apply div_nonneg (by linarith)
    have := update_den_pos hb hmc
    nlinarith
  have H1 : α * (1 - update a d) ≤ 1 - update a c := by
    rw [one_sub_update (update_den_pos ha ⟨hd0, hd1⟩).ne',
      one_sub_update (update_den_pos ha hc').ne']
    calc
      _ ≤ α * (k * (1 - a) / (1 + a * c)) := mul_le_mul_of_nonneg_left h1 hα
      _ = (α * k) * ((1 - a) / (1 + a * c)) := by ring
      _ ≤ (1 - c) * ((1 - a) / (1 + a * c)) := mul_le_mul_of_nonneg_right hαk hDa
      _ = _ := by ring
  have H2 : α * (1 + update b d) ≤ 1 + update b (-c) := by
    rw [one_add_update (update_den_pos hb ⟨hd0, hd1⟩).ne',
      one_add_update (update_den_pos hb hmc).ne']
    calc
      _ ≤ α * (k * (1 + b) / (1 - b * c)) := mul_le_mul_of_nonneg_left h2 hα
      _ = (α * k) * ((1 + b) / (1 - b * c)) := by ring
      _ ≤ (1 - c) * ((1 + b) / (1 - b * c)) := mul_le_mul_of_nonneg_right hαk hDb
      _ = _ := by simp only [mul_neg, ← sub_eq_add_neg]; ring
  refine ⟨d, hd0, hd1, ?_, ?_⟩
  · change update a c ≤ α * update a d + (1 - α)
    linarith
  · change α * update b d - (1 - α) ≤ update b (-c)
    linarith

end BufferedIsing.DSS

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical

theorem solution {a b c z : ℝ}
    (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1)
    (hab : b ≤ a) (hc : 0 ≤ c ∧ c < 1)
    (hz : 0 ≤ z) (hgap : a - b ≤ 2 * z) :
    ∃ d : ℝ, -1 < d ∧ d < 1 ∧
      update a c ≤ ((1 - c) / (1 + z * c)) * update a d +
        (1 - (1 - c) / (1 + z * c)) ∧
      ((1 - c) / (1 + z * c)) * update b d -
        (1 - (1 - c) / (1 + z * c)) ≤ update b (-c) := by
  first
    | exact OAI.BufferedIsing.DSS.interpolation ha hb hab hc hz hgap
    | exact OAI.BufferedIsing.DSS.interpolation
    | (apply OAI.BufferedIsing.DSS.interpolation <;> assumption)
    | (intros; apply OAI.BufferedIsing.DSS.interpolation <;> assumption)
