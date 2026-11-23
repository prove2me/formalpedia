-- Prove2me | solution 1 for IntegerRootsFN.Main.elementary_candidate_data
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:41:05.662671+00:00
-- url     : https://prove2.me/submissions/62e61e31-9c40-4e28-824a-0f62d779a5f4

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline

set_option autoImplicit false

namespace IntegerRootsFN.Main

private lemma logTwo_le_nat_of_le_two_pow {x : ℝ} {m : ℕ}
    (hx : 0 < x) (h : x ≤ (2 : ℝ) ^ m) : logTwo x ≤ (m : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hm := Real.log_le_log hx h
  rw [Real.log_pow] at hm
  unfold logTwo
  calc
    Real.log x / Real.log 2 ≤ ((m : ℝ) * Real.log 2) / Real.log 2 := by
      exact div_le_div_of_nonneg_right hm hlog2.le
    _ = (m : ℝ) := by field_simp

private lemma small_pointLength_le_two (z : ℤ) (hz : |z| ≤ 1) :
    pointLength z ≤ 2 := by
  apply Nat.ceil_le.mpr
  have hz' : (2 : ℝ) + |(z : ℝ)| ≤ 4 := by
    have hzi : |(z : ℝ)| ≤ 1 := by exact_mod_cast hz
    linarith
  have hpos : (0 : ℝ) < 2 + |(z : ℝ)| := by positivity
  have h := logTwo_le_nat_of_le_two_pow hpos (m := 2) (by norm_num at hz' ⊢; exact hz')
  norm_num at h ⊢
  exact h

end IntegerRootsFN.Main

open IntegerRootsFN.Main

theorem solution
    (hsearch : ElementarySearchContract) :
    ∃ Kcard Ksize : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
        (∀ r : ℤ, f.IsRoot r → r ∈ [-1, 0, 1] ++ searchCandidates f n b) ∧
        ([-1, 0, 1] ++ searchCandidates f n b).length ≤ Kcard * n ∧
        pointSize ([-1, 0, 1] ++ searchCandidates f n b) ≤ Ksize * b := by
  obtain ⟨M, C, hC, k, l, hsearch⟩ := hsearch
  refine ⟨24, 150, ?_⟩
  intro n b f hf
  obtain ⟨hn, hb, hdeg, hlead, hcoeff⟩ := hf
  obtain ⟨hcover, hlen, hsize, hrun⟩ := hsearch n b f ⟨hn, hb, hdeg, hlead, hcoeff⟩
  let cs : List ℤ := [-1, 0, 1] ++ searchCandidates f n b
  have hd_n : min n b ≤ n := min_le_left _ _
  have hd_b : min n b ≤ b := min_le_right _ _
  have hlog : logTwo (((min n b : ℕ) : ℝ) + 1) ≤ (b : ℝ) := by
    apply logTwo_le_nat_of_le_two_pow (by positivity)
    have hnat : min n b + 1 ≤ 2 ^ b := by
      calc
        min n b + 1 ≤ b + 1 := Nat.add_le_add_right hd_b 1
        _ ≤ 2 ^ b := Nat.succ_le_iff.mpr Nat.lt_two_pow_self
    exact_mod_cast hnat
  have hsmall : pointSize [-1, 0, 1] ≤ 6 := by
    have hm1 : pointLength (-1) ≤ 2 := small_pointLength_le_two _ (by norm_num)
    have h0 : pointLength 0 ≤ 2 := small_pointLength_le_two _ (by norm_num)
    have h1 : pointLength 1 ≤ 2 := small_pointLength_le_two _ (by norm_num)
    simp only [pointSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hcs_cover : ∀ r : ℤ, f.IsRoot r → r ∈ cs := by
    intro r hr
    by_cases hr2 : 2 ≤ |r|
    · exact List.mem_append_right _ (hcover r hr hr2)
    · have hrabs : |r| ≤ 1 := by omega
      have hrval : -1 ≤ r ∧ r ≤ 1 := abs_le.mp hrabs
      have hrvals : r = -1 ∨ r = 0 ∨ r = 1 := by omega
      apply List.mem_append_left
      simpa using hrvals
  have hcs_len : cs.length ≤ 24 * n := by
    change (([-1, 0, 1] : List ℤ) ++ searchCandidates f n b).length ≤ 24 * n
    rw [List.length_append]
    norm_num only [List.length_cons, List.length_nil]
    omega
  have hcs_size_real : (pointSize cs : ℝ) ≤ 150 * (b : ℝ) := by
    have happ : (pointSize cs : ℝ) =
        (pointSize [-1, 0, 1] : ℝ) + (pointSize (searchCandidates f n b) : ℝ) := by
      simp [cs, pointSize, Nat.cast_add, add_assoc]
    have hsmall_real : (pointSize [-1, 0, 1] : ℝ) ≤ 6 * (b : ℝ) := by
      have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have hs : (pointSize [-1, 0, 1] : ℝ) ≤ 6 := by exact_mod_cast hsmall
      nlinarith
    have hd_real : ((min n b : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hd_b
    calc
      (pointSize cs : ℝ) = (pointSize [-1, 0, 1] : ℝ) +
          (pointSize (searchCandidates f n b) : ℝ) := happ
      _ ≤ 6 * (b : ℝ) + 21 * (5 * ((min n b : ℕ) : ℝ) + (b : ℝ) +
          (1 : ℝ) / 2 * logTwo (((min n b : ℕ) : ℝ) + 1)) := add_le_add hsmall_real hsize
      _ ≤ 150 * (b : ℝ) := by nlinarith
  refine ⟨hcs_cover, hcs_len, ?_⟩
  exact_mod_cast hcs_size_real
