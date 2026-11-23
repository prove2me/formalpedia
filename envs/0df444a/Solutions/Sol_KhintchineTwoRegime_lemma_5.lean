-- Prove2me | solution 1 for KhintchineTwoRegime.lemma_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:56:53.521036+00:00
-- url     : https://prove2.me/submissions/16c64c71-1d0c-4ad2-adb9-509ab6209963
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_pad
import Definitions.Def_KhintchineTwoRegime_Phi
import Definitions.Def_KhintchineTwoRegime_IsProper
import Theorems.Thm_KhintchineTwoRegime_proper_unit_distance_sq
import Theorems.Thm_KhintchineTwoRegime_q_ge_one_of_le_four
import Theorems.Thm_KhintchineTwoRegime_lemma_5_from_decomposition

open HighDimProb.SparseRecovery (l2Norm)
open KhintchineTwoRegime

private lemma hasDerivAt_Aq (q x : ℝ) : HasDerivAt (Aq q) q x := by
  unfold Aq
  convert (hasDerivAt_const x (1 - q ^ 2)).add ((hasDerivAt_id x).const_mul q) using 1 <;>
    try {ext y; rfl} <;> ring

private lemma hasDerivAt_Bq (q x : ℝ) : HasDerivAt (Bq q) (q - 2 * x) x := by
  unfold Bq
  convert ((hasDerivAt_const x (1 - q ^ 2)).add
    ((hasDerivAt_id x).const_mul q)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
    try {ext y; rfl} <;> simp <;> ring

private lemma hasDerivAt_sqrt_Aq (q x : ℝ) (hA : 0 < Aq q x) :
    HasDerivAt (fun y => Real.sqrt (Aq q y))
      (q / (2 * Real.sqrt (Aq q x))) x := by
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hA)).comp x (hasDerivAt_Aq q x)
  convert h using 1 <;> try {ext y; rfl} <;> ring

private lemma hasDerivAt_sqrt_Bq (q x : ℝ) (hB : 0 < Bq q x) :
    HasDerivAt (fun y => Real.sqrt (Bq q y))
      ((q - 2 * x) / (2 * Real.sqrt (Bq q x))) x := by
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hB)).comp x (hasDerivAt_Bq q x)
  convert h using 1 <;> try {ext y; rfl} <;> ring

private lemma hasDerivAt_phi (q x : ℝ) (hA : 0 < Aq q x) (hB : 0 < Bq q x) :
    HasDerivAt (Phi q)
      (-3 / 8 + (q / (2 * Real.sqrt (Aq q x)) +
        (q - 2 * x) / Real.sqrt (Bq q x)) / (8 * Real.sqrt 2)) x := by
  have hl : HasDerivAt (fun y : ℝ => 3 / 4 * q - 3 / 8 * y) (-3 / 8) x := by
    convert (hasDerivAt_const x (3 / 4 * q)).sub
      ((hasDerivAt_id x).const_mul (3 / 8)) using 1 <;>
      try {ext y; rfl} <;> ring
  have hr : HasDerivAt
      (fun y => (Real.sqrt (Aq q y) + 2 * Real.sqrt (Bq q y)) / (8 * Real.sqrt 2))
      ((q / (2 * Real.sqrt (Aq q x)) + (q - 2 * x) / Real.sqrt (Bq q x)) /
        (8 * Real.sqrt 2)) x := by
    convert ((hasDerivAt_sqrt_Aq q x hA).add
      ((hasDerivAt_sqrt_Bq q x hB).const_mul 2)).div_const (8 * Real.sqrt 2) using 1 <;>
      try {ext y; rfl} <;> ring
  unfold Phi
  convert hl.add hr using 1 <;> try {ext y; rfl} <;> ring

theorem solution :
    (∀ n : ℕ, 2 ≤ n → ∀ τ : ℝ, ∀ ω ∈ Cn n τ, Real.sqrt (2 - Real.sqrt 2) < τ →
      pad ω 0 + pad ω 1 < 1 ∧
      Phi (pad ω 0 + pad ω 1) (pad ω 0 + pad ω 1 - pad ω 2 - pad ω 3) ≤ K n ω) ∧
    (∀ q : ℝ, |q| < 1 → (0 < deriv (Phi q) 0 ↔ 2 * Real.sqrt 2 / 3 < q)) ∧
    (∀ q x : ℝ, 0 < Aq q x → 0 < Bq q x → deriv (deriv (Phi q)) x ≤ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn τ ω hω hτ
    have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hd0sq : Real.sqrt (2 - Real.sqrt 2) ^ 2 = 2 - Real.sqrt 2 := by
      apply Real.sq_sqrt
      have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hroot_le : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sqrt_nonneg 2]
      linarith
    have htau2 : 2 - Real.sqrt 2 < τ ^ 2 := by
      have h := mul_self_lt_mul_self (Real.sqrt_nonneg (2 - Real.sqrt 2)) hτ
      nlinarith
    have hdist := proper_unit_distance_sq n hn τ ω hω
    have hqlt : pad ω 0 + pad ω 1 < 1 := by
      rw [hdist] at htau2
      have hp : 0 < Real.sqrt 2 * (1 - (pad ω 0 + pad ω 1)) := by nlinarith
      have hp' := (mul_pos_iff_of_pos_left hs2).mp hp
      linarith
    refine ⟨hqlt, ?_⟩
    by_cases hn4 : n ≤ 4
    · exact absurd hqlt (not_lt_of_ge (q_ge_one_of_le_four n hn hn4 ω hω.1))
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 4 := ⟨n - 4, by omega⟩
      simpa [pad] using lemma_5_from_decomposition m ω hω.1
  · intro q hq
    have hq2 : q ^ 2 < 1 := by
      have h := mul_self_lt_mul_self (abs_nonneg q) hq
      simpa [sq_abs, pow_two] using h
    have hh : 0 < 1 - q ^ 2 := by linarith
    have hs : 0 < Real.sqrt (1 - q ^ 2) := Real.sqrt_pos.2 hh
    have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hd : deriv (Phi q) 0 =
        3 * (q - 2 * Real.sqrt 2 * Real.sqrt (1 - q ^ 2)) /
          (16 * Real.sqrt 2 * Real.sqrt (1 - q ^ 2)) := by
      rw [(hasDerivAt_phi q 0 (by simpa [Aq] using hh) (by simpa [Bq] using hh)).deriv]
      simp only [Aq, Bq, mul_zero, add_zero, sub_zero]
      field_simp [ne_of_gt hr, ne_of_gt hs]
      <;> ring
    rw [hd]
    have hden : 0 < 16 * Real.sqrt 2 * Real.sqrt (1 - q ^ 2) := by positivity
    constructor
    · intro h
      have hnum : 0 < 3 * (q - 2 * Real.sqrt 2 * Real.sqrt (1 - q ^ 2)) :=
        (div_pos_iff_of_pos_right hden).mp h
      have hgt : 2 * Real.sqrt 2 * Real.sqrt (1 - q ^ 2) < q := by linarith
      have hqpos : 0 < q := lt_of_le_of_lt (by positivity) hgt
      have hsq := mul_self_lt_mul_self
        (show 0 ≤ 2 * Real.sqrt 2 * Real.sqrt (1 - q ^ 2) by positivity) hgt
      have hsquare : Real.sqrt (1 - q ^ 2) ^ 2 = 1 - q ^ 2 := Real.sq_sqrt hh.le
      by_contra! hle
      have hle' := mul_self_le_mul_self hqpos.le hle
      nlinarith
    · intro h
      have hc : 0 < 2 * Real.sqrt 2 / 3 := by positivity
      have hqpos : 0 < q := lt_trans hc h
      have hsq := mul_self_lt_mul_self hc.le h
      have hsquare : Real.sqrt (1 - q ^ 2) ^ 2 = 1 - q ^ 2 := Real.sq_sqrt hh.le
      have hgt : 2 * Real.sqrt 2 * Real.sqrt (1 - q ^ 2) < q := by
        by_contra! hle
        have hle' := mul_self_le_mul_self hqpos.le hle
        nlinarith
      apply (div_pos_iff_of_pos_right hden).mpr
      linarith
  · intro q x hA hB
    have hsA : 0 < Real.sqrt (Aq q x) := Real.sqrt_pos.2 hA
    have hsB : 0 < Real.sqrt (Bq q x) := Real.sqrt_pos.2 hB
    have hsA2 : Real.sqrt (Aq q x) ^ 2 = Aq q x := Real.sq_sqrt hA.le
    have hsB2 : Real.sqrt (Bq q x) ^ 2 = Bq q x := Real.sq_sqrt hB.le
    have hAo : IsOpen {y | 0 < Aq q y} :=
      isOpen_lt continuous_const (by unfold Aq; fun_prop)
    have hBo : IsOpen {y | 0 < Bq q y} :=
      isOpen_lt continuous_const (by unfold Bq; fun_prop)
    have heq : deriv (Phi q) =ᶠ[nhds x] fun y =>
        -3 / 8 + (q / (2 * Real.sqrt (Aq q y)) +
          (q - 2 * y) / Real.sqrt (Bq q y)) / (8 * Real.sqrt 2) := by
      filter_upwards [hAo.mem_nhds hA, hBo.mem_nhds hB] with y hyA hyB
      exact (hasDerivAt_phi q y hyA hyB).deriv
    have hN1 : HasDerivAt (fun y => q / (2 * Real.sqrt (Aq q y)))
        (-q ^ 2 / (4 * Aq q x * Real.sqrt (Aq q x))) x := by
      convert ((hasDerivAt_sqrt_Aq q x hA).inv (ne_of_gt hsA)).const_mul (q / 2) using 1 <;>
        first
        | rfl
        | (ext y <;> ring_nf <;> rfl)
        | (field_simp [ne_of_gt hA, ne_of_gt hsA] <;> rw [hsA2] <;> ring)
    have hnum : HasDerivAt (fun y : ℝ => q - 2 * y) (-2) x := by
      convert (hasDerivAt_const x q).sub ((hasDerivAt_id x).const_mul 2) using 1 <;>
        try {ext y; rfl} <;> ring
    have hN2 : HasDerivAt (fun y => (q - 2 * y) / Real.sqrt (Bq q y))
        (-2 / Real.sqrt (Bq q x) -
          (q - 2 * x) ^ 2 / (2 * Bq q x * Real.sqrt (Bq q x))) x := by
      convert hnum.div (hasDerivAt_sqrt_Bq q x hB) (ne_of_gt hsB) using 1 <;>
        first
        | rfl
        | (ext y <;> ring_nf <;> rfl)
        | (field_simp [ne_of_gt hB, ne_of_gt hsB] <;> rw [hsB2] <;> ring)
    have hD : HasDerivAt (fun y =>
        -3 / 8 + (q / (2 * Real.sqrt (Aq q y)) +
          (q - 2 * y) / Real.sqrt (Bq q y)) / (8 * Real.sqrt 2))
        ((-q ^ 2 / (4 * Aq q x * Real.sqrt (Aq q x)) +
          (-2 / Real.sqrt (Bq q x) -
            (q - 2 * x) ^ 2 / (2 * Bq q x * Real.sqrt (Bq q x)))) /
          (8 * Real.sqrt 2)) x := by
      convert ((hasDerivAt_const x (-3 / 8)).add
        ((hN1.add hN2).div_const (8 * Real.sqrt 2))) using 1 <;>
        try {ext y; rfl} <;> ring
    rw [heq.deriv_eq, hD.deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · have h1 : -q ^ 2 / (4 * Aq q x * Real.sqrt (Aq q x)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg q]) (by positivity)
      have h2 : -2 / Real.sqrt (Bq q x) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.sqrt_nonneg _)
      have h3 : -(q - 2 * x) ^ 2 / (2 * Bq q x * Real.sqrt (Bq q x)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
      have he : -q ^ 2 / (4 * Aq q x * Real.sqrt (Aq q x)) +
          (-2 / Real.sqrt (Bq q x) -
            (q - 2 * x) ^ 2 / (2 * Bq q x * Real.sqrt (Bq q x))) =
          -q ^ 2 / (4 * Aq q x * Real.sqrt (Aq q x)) +
            (-2 / Real.sqrt (Bq q x) +
              (-(q - 2 * x) ^ 2 / (2 * Bq q x * Real.sqrt (Bq q x)))) := by ring
      rw [he]
      exact add_nonpos h1 (add_nonpos h2 h3)
    · positivity
