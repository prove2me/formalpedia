-- Prove2me | solution 1 for OAI.ShortEgyptian.exists_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:58:57.610985+00:00
-- url     : https://prove2.me/submissions/006afce2-4fcd-458c-9da9-d9fc043a9054

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/GreedyExistence.lean:L7-L61
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.exists_expansion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Theorems.Thm_OAI_ShortEgyptian_quotient_spec

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem isExpansion_iff (a b : ℕ) (ns : List ℕ) :
    IsExpansion a b ns ↔ ns.Pairwise (· < ·) ∧
      (∀ n ∈ ns, 2 ≤ n) ∧ unitSum ns = (a : ℚ) / b := by
  have heq : (ns.map (fun n => (1 : ℚ) / (n : ℚ))).sum = unitSum ns := by
    induction ns with
    | nil => rfl
    | cons n ns ih => simpa [unitSum] using congrArg ((1 : ℚ) / (n : ℚ) + ·) ih
  simp only [IsExpansion, heq]

theorem residue_spec {v u : ℕ} (hv : 0 < v) (hu : 0 < u) :
    residue v u (quotient v u) < u ∧
      v + residue v u (quotient v u) = u * quotient v u := by
  obtain ⟨_, hlo, hhi⟩ := quotient_spec hv hu
  unfold residue
  omega

theorem unit_le_sum {n : ℕ} {ns : List ℕ} (hn : n ∈ ns) :
    (1 : ℚ) / n ≤ unitSum ns := by
  unfold unitSum
  apply List.single_le_sum _ _ (List.mem_map.mpr ⟨n, hn, rfl⟩)
  intro x hx
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
  positivity

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.GreedyExistence ----
namespace OAI

namespace ShortEgyptian

theorem exists_expansion (a b : ℕ) (hab : a < b) :
    ∃ ns : List ℕ, IsExpansion a b ns := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha0 : a = 0
    · subst a
      exact ⟨[], by simp [IsExpansion]⟩
    have ha : 0 < a := Nat.pos_of_ne_zero ha0
    have hb : 0 < b := lt_trans ha hab
    have haQ : (0 : ℚ) < a := by exact_mod_cast ha
    have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
    let z := quotient b a
    let r := residue b a z
    have hz : 0 < z := (quotient_spec hb ha).1
    have hzQ : (0 : ℚ) < z := by exact_mod_cast hz
    have hz2 : 2 ≤ z := by
      change 2 ≤ ⌈(b : ℚ) / a⌉₊
      apply Nat.succ_le_of_lt
      apply Nat.lt_ceil.mpr
      norm_num only [Nat.cast_one]
      apply (lt_div_iff₀ haQ).mpr
      simpa using (show (a : ℚ) < b by exact_mod_cast hab)
    have hrlt : r < a := (residue_spec hb ha).1
    have hre : b + r = a * z := (residue_spec hb ha).2
    have hbz : b ≤ b * z := by nlinarith
    have hrbz : r < b * z := lt_of_lt_of_le (lt_trans hrlt hab) hbz
    obtain ⟨ns, hns⟩ := ih r hrlt (b * z) hrbz
    rw [isExpansion_iff] at hns
    have hnseq : unitSum ns = (r : ℚ) / (b * z : ℕ) := hns.2.2
    have hrQ : (r : ℚ) < b := by exact_mod_cast (lt_trans hrlt hab)
    have hsmall : unitSum ns < (1 : ℚ) / z := by
      rw [hnseq, Nat.cast_mul]
      apply (div_lt_div_iff₀ (mul_pos hbQ hzQ) hzQ).mpr
      nlinarith
    have horder : ∀ n ∈ ns, z < n := by
      intro n hn
      have hn2 := hns.2.1 n hn
      have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
      by_contra h
      have hnz : (n : ℚ) ≤ z := by exact_mod_cast (Nat.le_of_not_gt h)
      have hdiv := one_div_le_one_div_of_le hnQ hnz
      have hsum := unit_le_sum hn
      linarith
    refine ⟨z :: ns, ?_⟩
    rw [isExpansion_iff]
    refine ⟨(List.pairwise_cons.mpr ⟨horder, hns.1⟩), ?_, ?_⟩
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hz2
      · exact hns.2.1 n hn
    · change (1 : ℚ) / z + unitSum ns = (a : ℚ) / b
      rw [hnseq, Nat.cast_mul]
      have heq : (b : ℚ) + r = a * z := by exact_mod_cast hre
      field_simp
      nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian


theorem solution : type_of% @_root_.OAI.ShortEgyptian.exists_expansion := @_root_.OAI.ShortEgyptian.exists_expansion
