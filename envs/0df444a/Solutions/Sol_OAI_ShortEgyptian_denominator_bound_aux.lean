-- Prove2me | solution 1 for OAI.ShortEgyptian.denominator_bound_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:00:52.810409+00:00
-- url     : https://prove2.me/submissions/306e8ed7-635b-4dbb-b807-addc71a1258b

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/LowerBound.lean:L18-L78
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.denominator_bound_aux. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem unit_le_sum {n : ℕ} {ns : List ℕ} (hn : n ∈ ns) :
    (1 : ℚ) / n ≤ unitSum ns := by
  unfold unitSum
  apply List.single_le_sum _ _ (List.mem_map.mpr ⟨n, hn, rfl⟩)
  intro x hx
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
  positivity

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.LowerBound ----
namespace OAI

namespace ShortEgyptian

theorem unitSum_le_length_div {d : ℕ} {ns : List ℕ}
    (hd : 0 < d) (hmin : ∀ n ∈ ns, d ≤ n) :
    unitSum ns ≤ (ns.length : ℚ) / d := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hh := (ns.map (fun n : ℕ => (1 : ℚ) / n)).sum_le_card_nsmul ((1 : ℚ) / d)
    (by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
      exact one_div_le_one_div_of_le hdQ (by exact_mod_cast hmin n hn))
  simpa [unitSum, div_eq_mul_inv] using hh

theorem denominator_bound_aux (ns : List ℕ) (hsort : ns.Pairwise (· ≤ ·))
    (hpos : ∀ n ∈ ns, 0 < n) (A P s : ℕ) (hA : 0 < A) (hP : 0 < P)
    (hlen : ns.length ≤ s) (heq : unitSum ns = (A : ℚ) / P) :
    ∀ n ∈ ns, n ≤ (s * P) ^ (2 ^ (ns.length - 1)) := by
  induction ns generalizing A P with
  | nil => simp
  | cons d ns ih =>
    have hd : 0 < d := hpos d (by simp)
    have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
    have hPQ : (0 : ℚ) < P := by exact_mod_cast hP
    have hAQ : (1 : ℚ) ≤ A := by exact_mod_cast hA
    have hsorted := List.pairwise_cons.mp hsort
    have hmin : ∀ n ∈ d :: ns, d ≤ n := by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact le_rfl
      · exact hsorted.1 n hn
    have hbd : (A : ℚ) / P ≤ (s : ℚ) / d := by
      rw [← heq]
      exact (unitSum_le_length_div hd hmin).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hlen) (le_of_lt hdQ))
    have hdpQ : (d : ℚ) ≤ s * P := by
      have hh := (div_le_div_iff₀ hPQ hdQ).mp hbd
      nlinarith
    have hdp : d ≤ s * P := by exact_mod_cast hdpQ
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hdp.trans (Nat.le_self_pow (by positivity) _)
    have hnslen : 0 < ns.length := List.length_pos_of_mem hn
    have hnpos : 0 < n := hpos n (by simp [hn])
    have hsumpos : 0 < unitSum ns :=
      (by positivity : (0 : ℚ) < 1 / (n : ℚ)).trans_le (unit_le_sum hn)
    have hAeq : (A : ℚ) / P = 1 / (d : ℚ) + unitSum ns := by
      simpa [unitSum_cons] using heq.symm
    have hPAQ : (P : ℚ) < A * d := by
      have hfrac : (1 : ℚ) / d < A / P := by linarith
      have hh := (div_lt_div_iff₀ hdQ hPQ).mp hfrac
      simpa using hh
    have hPA : P < A * d := by exact_mod_cast hPAQ
    have hr : 0 < A * d - P := Nat.sub_pos_of_lt hPA
    have hrem : unitSum ns = ((A * d - P : ℕ) : ℚ) / (P * d : ℕ) := by
      rw [Nat.cast_sub (le_of_lt hPA), Nat.cast_mul, Nat.cast_mul]
      apply (eq_div_iff (ne_of_gt (mul_pos hPQ hdQ))).mpr
      have hh := (div_eq_iff (ne_of_gt hPQ)).mp hAeq
      field_simp at hh ⊢
      nlinarith
    have ihb := ih hsorted.2 (fun x hx => hpos x (by simp [hx]))
      (A * d - P) (P * d) hr (Nat.mul_pos hP hd)
      (by simpa using (show ns.length ≤ s from by simpa using Nat.le_trans (Nat.le_succ ns.length) hlen))
      hrem n hn
    have hbase : s * (P * d) ≤ (s * P) ^ 2 := by nlinarith [hdp]
    calc
      n ≤ (s * (P * d)) ^ (2 ^ (ns.length - 1)) := ihb
      _ ≤ ((s * P) ^ 2) ^ (2 ^ (ns.length - 1)) := Nat.pow_le_pow_left hbase _
      _ = (s * P) ^ (2 ^ ((d :: ns).length - 1)) := by
        rw [← pow_mul]
        congr 1
        simp only [List.length_cons, Nat.add_sub_cancel]
        have hlen' : ns.length = ns.length - 1 + 1 := by omega
        conv_rhs => rw [hlen', pow_succ]
        omega

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian


theorem solution : type_of% @_root_.OAI.ShortEgyptian.denominator_bound_aux := @_root_.OAI.ShortEgyptian.denominator_bound_aux
