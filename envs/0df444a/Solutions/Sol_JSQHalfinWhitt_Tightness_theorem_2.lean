-- Prove2me | solution 1 for JSQHalfinWhitt.Tightness.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:24:45.747248+00:00
-- url     : https://prove2.me/submissions/ce0112d8-7cdd-480b-886c-3df900bb0904

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_1
import Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_2

namespace JSQHalfinWhitt.Tightness

open scoped Classical

section Coord

variable {n : ℕ}

lemma up_coord (q : State n) (i j : ℕ) :
    (up q i).1 j = if ArrivesAt q i ∧ j = i then q.1 j + 1 else q.1 j := by
  by_cases h : ArrivesAt q i
  · have : up q i = ⟨Function.update q.1 i (q.1 i + 1), up_mem q i h⟩ := dif_pos h
    rw [this]
    show Function.update q.1 i (q.1 i + 1) j = _
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj, Function.update_of_ne hj]
  · have : up q i = q := dif_neg h
    rw [this]; simp [h]

lemma down_coord (q : State n) (i j : ℕ) :
    (down q i).1 j = if q.1 (i + 1) < q.1 i ∧ j = i then q.1 j - 1 else q.1 j := by
  by_cases h : q.1 (i + 1) < q.1 i
  · have : down q i = ⟨Function.update q.1 i (q.1 i - 1), down_mem q i h⟩ := dif_pos h
    rw [this]
    show Function.update q.1 i (q.1 i - 1) j = _
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj, Function.update_of_ne hj]
  · have : down q i = q := dif_neg h
    rw [this]; simp [h]

lemma genQ_local (lam : ℝ) (f : State n → ℝ) (q : State n) (s : Finset ℕ)
    (hf : ∀ i ∉ s, f (up q i) = f q ∧ f (down q i) = f q) :
    genQ n lam f q = ∑ i ∈ s, (if ArrivesAt q i then (n : ℝ) * lam else 0) * (f (up q i) - f q) +
      ∑ i ∈ s, ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) * (f (down q i) - f q) := by
  unfold genQ
  rw [tsum_eq_sum (s := s), tsum_eq_sum (s := s)]
  · intro i hi; rw [(hf i hi).2]; simp
  · intro i hi; rw [(hf i hi).1]; simp

/-- generator on a single coordinate -/
lemma genQ_coord (lam : ℝ) (q : State n) (i : ℕ) :
    genQ n lam (fun q => (q.1 i : ℝ)) q =
      (if ArrivesAt q i then (n : ℝ) * lam else 0) - ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) := by
  rw [genQ_local lam _ q {i}]
  · simp only [Finset.sum_singleton]
    rw [up_coord, down_coord]
    by_cases h1 : ArrivesAt q i
    · by_cases h2 : q.1 (i + 1) < q.1 i
      · simp [h1, h2]; push_cast [Nat.cast_sub (by omega : 1 ≤ q.1 i)]; ring
      · have : q.1 (i+1) = q.1 i := le_antisymm (q.2.2.1 (Nat.le_succ i)) (by omega)
        simp [h1, h2, this]
    · by_cases h2 : q.1 (i + 1) < q.1 i
      · simp [h1, h2]; push_cast [Nat.cast_sub (by omega : 1 ≤ q.1 i)]; ring
      · have : q.1 (i+1) = q.1 i := le_antisymm (q.2.2.1 (Nat.le_succ i)) (by omega)
        simp [h1, h2, this]
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    rw [up_coord, down_coord]; simp [Ne.symm hj, hj]

end Coord

section Expect

variable {S : Type*}

lemma summable_bdd (π : S → ℝ) (hπ0 : ∀ q, 0 ≤ π q) (hπs : Summable π) (h : S → ℝ) (M : ℝ)
    (hb : ∀ q, |h q| ≤ M) : Summable (fun q => π q * h q) := by
  refine Summable.of_norm_bounded (g := fun q => M * π q) (hπs.mul_left M) (fun q => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 q)]
  nlinarith [hb q, hπ0 q, abs_nonneg (h q)]

lemma expect_sub' (π : S → ℝ) (h1 h2 : S → ℝ) (s1 : Summable (fun q => π q * h1 q))
    (s2 : Summable (fun q => π q * h2 q)) :
    expect π (fun q => h1 q - h2 q) = expect π h1 - expect π h2 := by
  unfold expect
  rw [← s1.tsum_sub s2]; congr 1; funext q; ring

lemma expect_add' (π : S → ℝ) (h1 h2 : S → ℝ) (s1 : Summable (fun q => π q * h1 q))
    (s2 : Summable (fun q => π q * h2 q)) :
    expect π (fun q => h1 q + h2 q) = expect π h1 + expect π h2 := by
  unfold expect
  rw [← s1.tsum_add s2]; congr 1; funext q; ring

lemma expect_cmul (π : S → ℝ) (c : ℝ) (h : S → ℝ) :
    expect π (fun q => c * h q) = c * expect π h := by
  unfold expect
  rw [← tsum_mul_left]; congr 1; funext q; ring

lemma expect_const (π : S → ℝ) (c : ℝ) (h1 : ∑' q, π q = 1) :
    expect π (fun _ => c) = c := by
  unfold expect
  rw [tsum_mul_right, h1, one_mul]

lemma expect_mono (π : S → ℝ) (hπ0 : ∀ q, 0 ≤ π q) (h1 h2 : S → ℝ)
    (s1 : Summable (fun q => π q * h1 q)) (s2 : Summable (fun q => π q * h2 q))
    (hle : ∀ q, h1 q ≤ h2 q) : expect π h1 ≤ expect π h2 := by
  unfold expect
  exact s1.tsum_le_tsum (fun q => mul_le_mul_of_nonneg_left (hle q) (hπ0 q)) s2

lemma prob_eq_expect (π : S → ℝ) (A : S → Prop) :
    prob π A = expect π (fun q => if A q then 1 else 0) := by
  unfold prob expect; congr 1; funext q; by_cases h : A q <;> simp [h]

end Expect


section Main

variable {n : ℕ}

lemma genQ_two (lam : ℝ) (g : ℝ → ℝ → ℝ) (q : State n) :
    genQ n lam (fun q => g (q.1 0 : ℝ) (q.1 1 : ℝ)) q =
      (if q.1 0 < n then (n : ℝ) * lam else 0) *
          (g ((q.1 0 : ℝ) + 1) (q.1 1 : ℝ) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) +
        (if q.1 0 = n ∧ q.1 1 < n then (n : ℝ) * lam else 0) *
          (g (q.1 0 : ℝ) ((q.1 1 : ℝ) + 1) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) +
        ((q.1 0 : ℝ) - (q.1 1 : ℝ)) *
          (g ((q.1 0 : ℝ) - 1) (q.1 1 : ℝ) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) +
        ((q.1 1 : ℝ) - (q.1 2 : ℝ)) *
          (g (q.1 0 : ℝ) ((q.1 1 : ℝ) - 1) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) := by
  rw [genQ_local lam _ q {0, 1}]
  · rw [Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)]
    beta_reduce
    have hA0 : ArrivesAt q 0 ↔ q.1 0 < n := by
      simp [ArrivesAt]
    have hA1 : ArrivesAt q 1 ↔ q.1 0 = n ∧ q.1 1 < n := by
      simp [ArrivesAt, Nat.lt_one_iff]
    have h10 : q.1 1 ≤ q.1 0 := q.2.2.1 (by norm_num)
    have h21 : q.1 2 ≤ q.1 1 := q.2.2.1 (by norm_num)
    have T0 : (if ArrivesAt q 0 then (n : ℝ) * lam else 0) *
        (g ((up q 0).1 0 : ℝ) ((up q 0).1 1 : ℝ) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) =
        (if q.1 0 < n then (n : ℝ) * lam else 0) *
          (g ((q.1 0 : ℝ) + 1) (q.1 1 : ℝ) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) := by
      by_cases h : ArrivesAt q 0
      · rw [if_pos h, if_pos (hA0.1 h), up_coord, up_coord, if_pos ⟨h, rfl⟩,
          if_neg (by simp)]
        push_cast; ring
      · rw [if_neg h, if_neg (fun h' => h (hA0.2 h'))]; ring
    have T1 : (if ArrivesAt q 1 then (n : ℝ) * lam else 0) *
        (g ((up q 1).1 0 : ℝ) ((up q 1).1 1 : ℝ) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) =
        (if q.1 0 = n ∧ q.1 1 < n then (n : ℝ) * lam else 0) *
          (g (q.1 0 : ℝ) ((q.1 1 : ℝ) + 1) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) := by
      by_cases h : ArrivesAt q 1
      · rw [if_pos h, if_pos (hA1.1 h), up_coord, up_coord, if_neg (by simp),
          if_pos ⟨h, rfl⟩]
        push_cast; ring
      · rw [if_neg h, if_neg (fun h' => h (hA1.2 h'))]; ring
    have D0 : ((q.1 0 : ℝ) - (q.1 (0 + 1) : ℝ)) *
        (g ((down q 0).1 0 : ℝ) ((down q 0).1 1 : ℝ) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) =
        ((q.1 0 : ℝ) - (q.1 1 : ℝ)) *
          (g ((q.1 0 : ℝ) - 1) (q.1 1 : ℝ) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) := by
      by_cases h : q.1 1 < q.1 0
      · rw [down_coord, down_coord, if_pos ⟨h, rfl⟩, if_neg (by simp)]
        push_cast [Nat.cast_sub (by omega : 1 ≤ q.1 0)]; ring
      · have e : q.1 1 = q.1 0 := by omega
        simp [e]
    have D1 : ((q.1 1 : ℝ) - (q.1 (1 + 1) : ℝ)) *
        (g ((down q 1).1 0 : ℝ) ((down q 1).1 1 : ℝ) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) =
        ((q.1 1 : ℝ) - (q.1 2 : ℝ)) *
          (g (q.1 0 : ℝ) ((q.1 1 : ℝ) - 1) - g (q.1 0 : ℝ) (q.1 1 : ℝ)) := by
      by_cases h : q.1 2 < q.1 1
      · rw [down_coord, down_coord, if_neg (by simp), if_pos ⟨h, rfl⟩]
        push_cast [Nat.cast_sub (by omega : 1 ≤ q.1 1)]; ring
      · have e : q.1 2 = q.1 1 := by omega
        simp [e]
    rw [T0, T1, D0, D1]; ring
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    constructor
    · simp only [up_coord]; simp [Ne.symm hi.1, Ne.symm hi.2]
    · simp only [down_coord]; simp [Ne.symm hi.1, Ne.symm hi.2]

end Main

section Main2

variable {S : Type*}

lemma lin_le5 (π : S → ℝ) (hπ0 : ∀ q, 0 ≤ π q) (h u1 u2 u3 u4 u5 : S → ℝ)
    (c1 c2 c3 c4 c5 : ℝ) (sh : Summable (fun q => π q * h q))
    (s1 : Summable (fun q => π q * u1 q)) (s2 : Summable (fun q => π q * u2 q))
    (s3 : Summable (fun q => π q * u3 q)) (s4 : Summable (fun q => π q * u4 q))
    (s5 : Summable (fun q => π q * u5 q))
    (hpt : ∀ q, h q ≤ c1 * u1 q + c2 * u2 q + c3 * u3 q + c4 * u4 q + c5 * u5 q) :
    expect π h ≤ c1 * expect π u1 + c2 * expect π u2 + c3 * expect π u3 +
      c4 * expect π u4 + c5 * expect π u5 := by
  unfold expect
  have t1 := s1.mul_left c1
  have t2 := s2.mul_left c2
  have t3 := s3.mul_left c3
  have t4 := s4.mul_left c4
  have t5 := s5.mul_left c5
  have hs := (((t1.add t2).add t3).add t4).add t5
  have := sh.tsum_le_tsum (f := fun q => π q * h q) (g := fun q =>
      c1 * (π q * u1 q) + c2 * (π q * u2 q) + c3 * (π q * u3 q) + c4 * (π q * u4 q) +
        c5 * (π q * u5 q))
    (fun q => by
      have := mul_le_mul_of_nonneg_left (hpt q) (hπ0 q)
      linarith [this]) hs
  have heq : ∑' q, (c1 * (π q * u1 q) + c2 * (π q * u2 q) + c3 * (π q * u3 q) +
      c4 * (π q * u4 q) + c5 * (π q * u5 q)) = c1 * ∑' q, π q * u1 q + c2 * ∑' q, π q * u2 q +
      c3 * ∑' q, π q * u3 q + c4 * ∑' q, π q * u4 q + c5 * ∑' q, π q * u5 q := by
    rw [(((t1.add t2).add t3).add t4).tsum_add t5, ((t1.add t2).add t3).tsum_add t4,
      (t1.add t2).tsum_add t3, t1.tsum_add t2, tsum_mul_left, tsum_mul_left, tsum_mul_left,
      tsum_mul_left, tsum_mul_left]
  linarith

end Main2

section Main3

variable {n : ℕ}

lemma summ3 (π : State n → ℝ) (hπ0 : ∀ q, 0 ≤ π q) (hπs : Summable π)
    (h : ℕ → ℕ → ℕ → ℝ) : Summable (fun q : State n => π q * h (q.1 0) (q.1 1) (q.1 2)) := by
  refine summable_bdd π hπ0 hπs _
    (∑ x ∈ Finset.range (n+1) ×ˢ Finset.range (n+1) ×ˢ Finset.range (n+1),
      |h x.1 x.2.1 x.2.2|) (fun q => ?_)
  have hm : (q.1 0, q.1 1, q.1 2) ∈
      Finset.range (n+1) ×ˢ Finset.range (n+1) ×ˢ Finset.range (n+1) := by
    have := q.2.1 0; have := q.2.1 1; have := q.2.1 2
    simp only [Finset.mem_product, Finset.mem_range]; omega
  exact Finset.single_le_sum (f := fun x : ℕ × ℕ × ℕ => |h x.1 x.2.1 x.2.2|)
    (fun _ _ => abs_nonneg _) hm

lemma EG0 (hn : 1 ≤ n) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : State n → ℝ) (hπ : IsStationaryDist (genQ n lam) π) (g : ℝ → ℝ → ℝ) :
    Summable (fun q => π q * genQ n lam (fun q => g (q.1 0 : ℝ) (q.1 1 : ℝ)) q) ∧
      expect π (genQ n lam (fun q => g (q.1 0 : ℝ) (q.1 1 : ℝ))) = 0 :=
  lemma_1 n lam hn hlam0 hlam1 π hπ _
    (summ3 π hπ.1 hπ.2.1 (fun a b _ => |g (a : ℝ) (b : ℝ)|))

lemma natfacts (q : State n) :
    (q.1 0 : ℝ) ≤ n ∧ (q.1 1 : ℝ) ≤ q.1 0 ∧ (q.1 2 : ℝ) ≤ q.1 1 ∧ (0 : ℝ) ≤ q.1 2 := by
  refine ⟨by exact_mod_cast q.2.1 0, by exact_mod_cast q.2.2.1 (by norm_num : 0 ≤ 1),
    by exact_mod_cast q.2.2.1 (by norm_num : 1 ≤ 2), by positivity⟩

lemma pw1 (lam β s : ℝ) (hL : (n : ℝ) * lam = n - β * s) (hL0 : 0 ≤ (n : ℝ) * lam)
    (hLn : (n : ℝ) * lam ≤ n) (q : State n) :
    2 * (((n : ℝ) - q.1 0) * q.1 1) ≤ (2 * β * s * n + 2 * n) * 1 + (-2 * β * s) * (q.1 0 : ℝ) +
      (-1) * genQ n lam (fun q => (fun x y : ℝ => ((n : ℝ) - x) ^ 2) (q.1 0 : ℝ) (q.1 1 : ℝ)) q +
      0 * 1 + 0 * 1 := by
  rw [genQ_two lam (fun x y : ℝ => ((n : ℝ) - x) ^ 2) q]
  beta_reduce
  obtain ⟨h1, h2, h3, h4⟩ := natfacts q
  split_ifs with e1 e2 e2
  · omega
  · have : ((q.1 0 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast e1
    nlinarith
  · have : ((q.1 0 : ℕ) : ℝ) = n := by exact_mod_cast e2.1
    rw [this]; nlinarith
  · have := q.2.1 0
    have : q.1 0 = n := by omega
    have : ((q.1 0 : ℕ) : ℝ) = n := by exact_mod_cast this
    rw [this]; nlinarith

lemma three_cases (q : State n) :
    q.1 0 < n ∨ (q.1 0 = n ∧ q.1 1 < n) ∨ (q.1 0 = n ∧ q.1 1 = n) := by
  have := q.2.1 0; have := q.2.1 1; omega

lemma I2_cases (q : State n) :
    ((∀ j, j < 2 → q.1 j = n) ↔ (q.1 0 = n ∧ q.1 1 = n)) := by
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ j hj
    interval_cases j <;> assumption

lemma pw2 (lam β s : ℝ) (hL : (n : ℝ) * lam = n - β * s) (hL0 : 0 ≤ (n : ℝ) * lam)
    (hLn : (n : ℝ) * lam ≤ n) (q : State n) :
    (β * s) * (q.1 1 : ℝ) ≤ 2 * (((n : ℝ) - q.1 0) * q.1 1) + 1 * (q.1 1 : ℝ) +
      (n : ℝ) * (q.1 2 : ℝ) +
      (-((n : ℝ) * lam * n)) * (if ∀ j, j < 2 → q.1 j = n then (1 : ℝ) else 0) +
      1 * genQ n lam (fun q => (fun x y : ℝ => ((n : ℝ) - x) * y - y ^ 2 / 2 + y / 2)
        (q.1 0 : ℝ) (q.1 1 : ℝ)) q := by
  rw [genQ_two lam (fun x y : ℝ => ((n : ℝ) - x) * y - y ^ 2 / 2 + y / 2) q]
  beta_reduce
  obtain ⟨h1, h2, h3, h4⟩ := natfacts q
  have hqn := q.2.1 0
  rw [I2_cases]
  rcases three_cases q with e1 | e2 | e3
  · have n1 : ¬ (q.1 0 = n ∧ q.1 1 < n) := by omega
    have n2 : ¬ (q.1 0 = n ∧ q.1 1 = n) := by omega
    rw [if_pos e1, if_neg n1, if_neg n2]
    have : ((q.1 0 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast e1
    nlinarith [mul_nonneg h4 (sub_nonneg.2 h3), mul_nonneg h4 (by linarith : (0:ℝ) ≤ n - q.1 0),
      mul_nonneg h4 (by linarith : (0:ℝ) ≤ n - q.1 1)]
  · have n1 : ¬ (q.1 0 < n) := by omega
    have n2 : ¬ (q.1 0 = n ∧ q.1 1 = n) := by omega
    rw [if_pos e2, if_neg n1, if_neg n2]
    have ea : ((q.1 0 : ℕ) : ℝ) = n := by exact_mod_cast e2.1
    rw [ea]
    nlinarith [mul_nonneg h4 (sub_nonneg.2 h3), mul_nonneg h4 (by linarith : (0:ℝ) ≤ n - q.1 1)]
  · have n1 : ¬ (q.1 0 < n) := by omega
    have n2 : ¬ (q.1 0 = n ∧ q.1 1 < n) := by omega
    rw [if_pos e3, if_neg n1, if_neg n2]
    have ea : ((q.1 0 : ℕ) : ℝ) = n := by exact_mod_cast e3.1
    have eb : ((q.1 1 : ℕ) : ℝ) = n := by exact_mod_cast e3.2
    rw [ea, eb]
    nlinarith

lemma pw3 (lam β s : ℝ) (hL : (n : ℝ) * lam = n - β * s) (hL0 : 0 ≤ (n : ℝ) * lam)
    (hLn : (n : ℝ) * lam ≤ n) (q : State n) :
    (β * s) * ((q.1 1 : ℝ) ^ 2) ≤ 3 * (((n : ℝ) - q.1 0) * (q.1 1 : ℝ) ^ 2) +
      2 * ((q.1 1 : ℝ) ^ 2) + ((n : ℝ) ^ 2) * (q.1 2 : ℝ) +
      (-((n : ℝ) * lam * n ^ 2)) * (if ∀ j, j < 2 → q.1 j = n then (1 : ℝ) else 0) +
      1 * genQ n lam (fun q => (fun x y : ℝ => ((n : ℝ) - x) * y ^ 2 - y ^ 3 / 3 + y ^ 2 / 2)
        (q.1 0 : ℝ) (q.1 1 : ℝ)) q := by
  rw [genQ_two lam (fun x y : ℝ => ((n : ℝ) - x) * y ^ 2 - y ^ 3 / 3 + y ^ 2 / 2) q]
  beta_reduce
  obtain ⟨h1, h2, h3, h4⟩ := natfacts q
  have hqn := q.2.1 0
  rw [I2_cases]
  rcases three_cases q with e1 | e2 | e3
  · have n1 : ¬ (q.1 0 = n ∧ q.1 1 < n) := by omega
    have n2 : ¬ (q.1 0 = n ∧ q.1 1 = n) := by omega
    rw [if_pos e1, if_neg n1, if_neg n2]
    have : ((q.1 0 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast e1
    have hz : (0:ℝ) ≤ n - q.1 0 := by linarith
    have hb0 : (0:ℝ) ≤ q.1 1 := by linarith
    nlinarith [mul_nonneg h4 (sub_nonneg.2 h3), mul_nonneg hz (sub_nonneg.2 h3),
      mul_nonneg (mul_nonneg h4 hz) hb0, mul_nonneg h4 hb0,
      mul_nonneg h4 (by nlinarith : (0:ℝ) ≤ (n:ℝ)^2 - (q.1 1 : ℝ)^2)]
  · have n1 : ¬ (q.1 0 < n) := by omega
    have n2 : ¬ (q.1 0 = n ∧ q.1 1 = n) := by omega
    rw [if_pos e2, if_neg n1, if_neg n2]
    have ea : ((q.1 0 : ℕ) : ℝ) = n := by exact_mod_cast e2.1
    rw [ea]
    have hb0 : (0:ℝ) ≤ q.1 1 := by linarith
    nlinarith [mul_nonneg h4 (sub_nonneg.2 h3), mul_nonneg h4 hb0,
      mul_nonneg h4 (by nlinarith : (0:ℝ) ≤ (n:ℝ)^2 - (q.1 1 : ℝ)^2)]
  · have n1 : ¬ (q.1 0 < n) := by omega
    have n2 : ¬ (q.1 0 = n ∧ q.1 1 < n) := by omega
    rw [if_pos e3, if_neg n1, if_neg n2]
    have ea : ((q.1 0 : ℕ) : ℝ) = n := by exact_mod_cast e3.1
    have eb : ((q.1 1 : ℕ) : ℝ) = n := by exact_mod_cast e3.2
    rw [ea, eb]
    rw [eb] at h3
    nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ n)]

lemma pw4 (lam β s : ℝ) (hL : (n : ℝ) * lam = n - β * s) (hL0 : 0 ≤ (n : ℝ) * lam)
    (hLn : (n : ℝ) * lam ≤ n) (q : State n) :
    2 * (((n : ℝ) - q.1 0) * (q.1 1 : ℝ) ^ 2) ≤ (2 * n) * (q.1 1 : ℝ) +
      (2 * β * s) * (((n : ℝ) - q.1 0) * q.1 1) +
      (-1) * genQ n lam (fun q => (fun x y : ℝ => ((n : ℝ) - x) ^ 2 * y)
        (q.1 0 : ℝ) (q.1 1 : ℝ)) q + 0 * 1 + 0 * 1 := by
  rw [genQ_two lam (fun x y : ℝ => ((n : ℝ) - x) ^ 2 * y) q]
  beta_reduce
  obtain ⟨h1, h2, h3, h4⟩ := natfacts q
  have hqn := q.2.1 0
  split_ifs with e1 e2 e2
  · omega
  · have : ((q.1 0 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast e1
    have hz : (0:ℝ) ≤ n - q.1 0 := by linarith
    have hb0 : (0:ℝ) ≤ q.1 1 := by linarith
    nlinarith [mul_nonneg (mul_nonneg hz hz) (sub_nonneg.2 h3), mul_nonneg (mul_nonneg hz hz) hb0,
      mul_nonneg hz hb0, mul_nonneg hb0 hb0, mul_nonneg (by linarith : (0:ℝ) ≤ n - n * lam) hb0]
  · have ea : ((q.1 0 : ℕ) : ℝ) = n := by exact_mod_cast e2.1
    rw [ea]
    have hb0 : (0:ℝ) ≤ q.1 1 := by linarith
    nlinarith [mul_nonneg hb0 hb0, mul_nonneg hb0 (by linarith : (0:ℝ) ≤ n)]
  · have : q.1 0 = n := by omega
    have ea : ((q.1 0 : ℕ) : ℝ) = n := by exact_mod_cast this
    rw [ea]
    have hb0 : (0:ℝ) ≤ q.1 1 := by linarith
    nlinarith [mul_nonneg hb0 hb0, mul_nonneg hb0 (by linarith : (0:ℝ) ≤ n)]

lemma pw5 (lam : ℝ) (hL0 : 0 ≤ (n : ℝ) * lam) (hLn : (n : ℝ) * lam ≤ n) (q : State n) :
    ((n : ℝ) * lam * n) * (if ∀ j, j < 2 → q.1 j = n then (1 : ℝ) else 0) ≤
      1 * ((q.1 1 : ℝ) ^ 2) + 0 * 1 + 0 * 1 + 0 * 1 + 0 * 1 := by
  rw [I2_cases]
  split_ifs with e
  · have eb : ((q.1 1 : ℕ) : ℝ) = n := by exact_mod_cast e.2
    rw [eb]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · nlinarith [sq_nonneg (q.1 1 : ℝ)]

lemma arith_main (β s N lam A B Cc P2 Ezb Eb2 Ezb2 : ℝ) (hβ : 0 < β) (hs0 : 0 < s)
    (hss : s * s = N) (hL : N * lam = N - β * s)
    (st1 : 2 * Ezb ≤ (2 * β * s * N + 2 * N) * 1 + (-2 * β * s) * A + (-1) * 0 + 0 * 1 + 0 * 1)
    (hA : A = N * lam)
    (st2 : β * s * B ≤ 2 * Ezb + 1 * B + N * Cc + (-(N * lam * N)) * P2 + 1 * 0)
    (st3 : β * s * Eb2 ≤ 3 * Ezb2 + 2 * Eb2 + N ^ 2 * Cc + (-(N * lam * N ^ 2)) * P2 + 1 * 0)
    (st4 : 2 * Ezb2 ≤ 2 * N * B + 2 * β * s * Ezb + (-1) * 0 + 0 * 1 + 0 * 1)
    (st5 : N * lam * N * P2 ≤ 1 * Eb2 + 0 * 1 + 0 * 1 + 0 * 1 + 0 * 1)
    (stB : B ≤ N * 1 + 0 * 1 + 0 * 1 + 0 * 1 + 0 * 1)
    (stC : Cc ≤ N * 1 + 0 * 1 + 0 * 1 + 0 * 1 + 0 * 1)
    (hCc : Cc = N * lam * P2) (hB0 : 0 ≤ B) (hEb20 : 0 ≤ Eb2) :
    B ≤ (4 * β ^ 2 + 6) / β * s ∧
      Cc ≤ 6 * ((4 * β ^ 2 + 6) / β) / β + 6 * (β ^ 2 + 1) + 16 / β ^ 2 := by
  set C2 := (4 * β ^ 2 + 6) / β with hC2
  have hN : 0 < N := by rw [← hss]; positivity
  have hβs : 0 < β * s := by positivity
  have hbs2 : β * s * (β * s) = β ^ 2 * N := by rw [← hss]; ring
  have hEzb : Ezb ≤ (β ^ 2 + 1) * N := by
    have : 2 * Ezb ≤ 2 * (β * s) * (N - A) + 2 * N := by linarith
    rw [hA, hL] at this
    have : 2 * Ezb ≤ 2 * (β * s * (β * s)) + 2 * N := by linarith
    rw [hbs2] at this; linarith
  have hBb : β * s * B ≤ 2 * Ezb + B := by
    have : N * Cc + (-(N * lam * N)) * P2 = 0 := by rw [hCc]; ring
    linarith
  have hBC2 : B ≤ C2 * s := by
    rcases le_or_gt 2 (β * s) with h2 | h2
    · have h0 : (β * s - 1) * B ≤ 2 * (β ^ 2 + 1) * N := by linarith
      have h1 : (β * s / 2) * B ≤ (β * s - 1) * B :=
        mul_le_mul_of_nonneg_right (by linarith) hB0
      have : β * s * B ≤ β * s * (C2 * s) := by
        have e : β * s * (C2 * s) = (4 * β ^ 2 + 6) * N := by
          rw [hC2, ← hss]; field_simp
        rw [e]; nlinarith
      exact le_of_mul_le_mul_left this hβs
    · have hsC : s ≤ C2 := by
        rw [hC2, le_div_iff₀ hβ]; nlinarith
      have : N ≤ C2 * s := by
        rw [← hss]; exact mul_le_mul_of_nonneg_right hsC hs0.le
      linarith
  refine ⟨hBC2, ?_⟩
  rcases le_or_gt 4 (β * s) with h4 | h4
  · have hNC : N * Cc ≤ Eb2 := by rw [hCc]; linarith
    have hE2 : β * s * Eb2 ≤ 3 * Ezb2 + 2 * Eb2 := by
      have : N ^ 2 * Cc + (-(N * lam * N ^ 2)) * P2 = 0 := by rw [hCc]; ring
      linarith
    have hE4 : (β * s - 2) * Eb2 ≤ 3 * N * B + 3 * (β * s) * Ezb := by linarith
    have h1 : (β * s / 2) * Eb2 ≤ (β * s - 2) * Eb2 :=
      mul_le_mul_of_nonneg_right (by linarith) hEb20
    have hb1 : 3 * N * B ≤ 3 * N * (C2 * s) :=
      mul_le_mul_of_nonneg_left hBC2 (by positivity)
    have hb2 : 3 * (β * s) * Ezb ≤ 3 * (β * s) * ((β ^ 2 + 1) * N) :=
      mul_le_mul_of_nonneg_left hEzb (by positivity)
    have hE5 : β * s * Eb2 ≤ β * s * (N * (6 * C2 / β + 6 * (β ^ 2 + 1))) := by
      have e : β * s * (N * (6 * C2 / β + 6 * (β ^ 2 + 1))) =
          2 * (3 * N * (C2 * s)) + 2 * (3 * (β * s) * ((β ^ 2 + 1) * N)) := by
        field_simp; ring
      rw [e]; linarith
    have hE6 := le_of_mul_le_mul_left hE5 hβs
    have : N * Cc ≤ N * (6 * C2 / β + 6 * (β ^ 2 + 1)) := hNC.trans hE6
    have := le_of_mul_le_mul_left this hN
    have : 0 ≤ 16 / β ^ 2 := by positivity
    linarith
  · have : N < 16 / β ^ 2 := by
      rw [lt_div_iff₀ (by positivity), ← hss]; nlinarith
    have : 0 ≤ 6 * C2 / β + 6 * (β ^ 2 + 1) := by positivity
    linarith

theorem theorem_2_proof (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → β < Real.sqrt n →
      ∀ π : State n → ℝ, IsStationaryDist (genQ n (lamHW β n)) π →
        (expect π (fun q => |Real.sqrt n * (((q.1 0 : ℝ) - n) / n)|) ≤ C ∧
          expect π (fun q => |Real.sqrt n * ((q.1 1 : ℝ) / n)|) ≤ C) ∧
        ∀ i : ℕ, 2 ≤ i → expect π (fun q => |(n : ℝ) * ((q.1 i : ℝ) / n)|) ≤ C := by
  have hC2p : 0 ≤ (4 * β ^ 2 + 6) / β := by positivity
  have hC3p : 0 ≤ 6 * ((4 * β ^ 2 + 6) / β) / β + 6 * (β ^ 2 + 1) := by positivity
  have h16 : 0 ≤ 16 / β ^ 2 := by positivity
  refine ⟨β + (4 * β ^ 2 + 6) / β + (6 * ((4 * β ^ 2 + 6) / β) / β + 6 * (β ^ 2 + 1) +
    16 / β ^ 2), ?_⟩
  intro n hn hβn π hπ
  have hπ0 := hπ.1
  have hπs := hπ.2.1
  have hπ1 := hπ.2.2.1
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hN
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hN.le
  have hL : (n : ℝ) * lamHW β n = n - β * Real.sqrt n := by
    rw [lamHW, mul_sub, mul_one]
    have : (n : ℝ) * (β / Real.sqrt n) = β * Real.sqrt n := by
      rw [mul_div_assoc', div_eq_iff hs0.ne']; linear_combination (-β) * hss
    rw [this]
  have hlam0 : 0 < lamHW β n := by
    rw [lamHW, sub_pos, div_lt_one hs0]; exact hβn
  have hlam1 : lamHW β n < 1 := by
    rw [lamHW]; have : 0 < β / Real.sqrt n := by positivity
    linarith
  have hL0 : 0 ≤ (n : ℝ) * lamHW β n := by positivity
  have hLn : (n : ℝ) * lamHW β n ≤ n := by nlinarith
  obtain ⟨hA, hrest⟩ := lemma_2 n (lamHW β n) hn hlam0 hlam1 π hπ
  have hCc := hrest 2 (by norm_num)
  rw [prob_eq_expect] at hCc
  have S1 := summ3 π hπ0 hπs (fun _ _ _ => (1 : ℝ))
  have Sa := summ3 π hπ0 hπs (fun a _ _ => (a : ℝ))
  have Sb := summ3 π hπ0 hπs (fun _ b _ => (b : ℝ))
  have Sc := summ3 π hπ0 hπs (fun _ _ c => (c : ℝ))
  have Szb := summ3 π hπ0 hπs (fun a b _ => ((n : ℝ) - a) * b)
  have Sb2 := summ3 π hπ0 hπs (fun _ b _ => (b : ℝ) ^ 2)
  have Szb2 := summ3 π hπ0 hπs (fun a b _ => ((n : ℝ) - a) * (b : ℝ) ^ 2)
  have SI2 := summ3 π hπ0 hπs (fun a b _ => if a = n ∧ b = n then (1 : ℝ) else 0)
  have SI2' : Summable (fun q : State n => π q *
      (if ∀ j, j < 2 → q.1 j = n then (1 : ℝ) else 0)) := by
    refine SI2.congr (fun q => ?_)
    simp only [I2_cases]
  have E1 : expect π (fun _ => (1 : ℝ)) = 1 := expect_const π 1 hπ1
  obtain ⟨SG1, EG1⟩ := EG0 hn (lamHW β n) hlam0 hlam1 π hπ (fun x y : ℝ => ((n : ℝ) - x) ^ 2)
  obtain ⟨SG2, EG2⟩ := EG0 hn (lamHW β n) hlam0 hlam1 π hπ
    (fun x y : ℝ => ((n : ℝ) - x) * y - y ^ 2 / 2 + y / 2)
  obtain ⟨SG3, EG3⟩ := EG0 hn (lamHW β n) hlam0 hlam1 π hπ
    (fun x y : ℝ => ((n : ℝ) - x) * y ^ 2 - y ^ 3 / 3 + y ^ 2 / 2)
  obtain ⟨SG4, EG4⟩ := EG0 hn (lamHW β n) hlam0 hlam1 π hπ
    (fun x y : ℝ => ((n : ℝ) - x) ^ 2 * y)
  have hB0 : 0 ≤ expect π (fun q => (q.1 1 : ℝ)) :=
    tsum_nonneg (fun q => mul_nonneg (hπ0 q) (by positivity))
  have hEb20 : 0 ≤ expect π (fun q => (q.1 1 : ℝ) ^ 2) :=
    tsum_nonneg (fun q => mul_nonneg (hπ0 q) (by positivity))
  have st1 := lin_le5 π hπ0 (fun q => 2 * (((n : ℝ) - q.1 0) * q.1 1)) (fun _ => 1)
    (fun q => (q.1 0 : ℝ))
    (genQ n (lamHW β n) (fun q => (fun x y : ℝ => ((n : ℝ) - x) ^ 2) (q.1 0 : ℝ) (q.1 1 : ℝ)))
    (fun _ => 1) (fun _ => 1) _ _ _ _ _ (Szb.mul_left 2 |>.congr (fun q => by ring))
    S1 Sa SG1 S1 S1 (pw1 (lamHW β n) β (Real.sqrt n) hL hL0 hLn)
  rw [expect_cmul, E1, EG1] at st1
  have st2 := lin_le5 π hπ0 (fun q => (β * Real.sqrt n) * (q.1 1 : ℝ))
    (fun q => ((n : ℝ) - q.1 0) * q.1 1) (fun q => (q.1 1 : ℝ)) (fun q => (q.1 2 : ℝ))
    (fun q => if ∀ j, j < 2 → q.1 j = n then (1 : ℝ) else 0)
    (genQ n (lamHW β n) (fun q => (fun x y : ℝ => ((n : ℝ) - x) * y - y ^ 2 / 2 + y / 2)
      (q.1 0 : ℝ) (q.1 1 : ℝ))) _ _ _ _ _
    (Sb.mul_left (β * Real.sqrt n) |>.congr (fun q => by ring)) Szb Sb Sc SI2' SG2
    (pw2 (lamHW β n) β (Real.sqrt n) hL hL0 hLn)
  rw [expect_cmul, EG2] at st2
  have st3 := lin_le5 π hπ0 (fun q => (β * Real.sqrt n) * ((q.1 1 : ℝ) ^ 2))
    (fun q => ((n : ℝ) - q.1 0) * (q.1 1 : ℝ) ^ 2) (fun q => (q.1 1 : ℝ) ^ 2)
    (fun q => (q.1 2 : ℝ))
    (fun q => if ∀ j, j < 2 → q.1 j = n then (1 : ℝ) else 0)
    (genQ n (lamHW β n) (fun q => (fun x y : ℝ => ((n : ℝ) - x) * y ^ 2 - y ^ 3 / 3 + y ^ 2 / 2)
      (q.1 0 : ℝ) (q.1 1 : ℝ))) _ _ _ _ _
    (Sb2.mul_left (β * Real.sqrt n) |>.congr (fun q => by ring)) Szb2 Sb2 Sc SI2' SG3
    (pw3 (lamHW β n) β (Real.sqrt n) hL hL0 hLn)
  rw [expect_cmul, EG3] at st3
  have st4 := lin_le5 π hπ0 (fun q => 2 * (((n : ℝ) - q.1 0) * (q.1 1 : ℝ) ^ 2))
    (fun q => (q.1 1 : ℝ)) (fun q => ((n : ℝ) - q.1 0) * q.1 1)
    (genQ n (lamHW β n) (fun q => (fun x y : ℝ => ((n : ℝ) - x) ^ 2 * y) (q.1 0 : ℝ) (q.1 1 : ℝ)))
    (fun _ => 1) (fun _ => 1) _ _ _ _ _
    (Szb2.mul_left 2 |>.congr (fun q => by ring)) Sb Szb SG4 S1 S1
    (pw4 (lamHW β n) β (Real.sqrt n) hL hL0 hLn)
  rw [expect_cmul, EG4, E1] at st4
  have st5 := lin_le5 π hπ0
    (fun q => ((n : ℝ) * lamHW β n * n) * (if ∀ j, j < 2 → q.1 j = n then (1 : ℝ) else 0))
    (fun q => (q.1 1 : ℝ) ^ 2) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) _ _ _ _ _
    (SI2'.mul_left ((n : ℝ) * lamHW β n * n) |>.congr (fun q => by ring)) Sb2 S1 S1 S1 S1
    (pw5 (lamHW β n) hL0 hLn)
  rw [expect_cmul, E1] at st5
  have stB := lin_le5 π hπ0 (fun q => (q.1 1 : ℝ)) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (n : ℝ) 0 0 0 0 Sb S1 S1 S1 S1 S1
    (fun q => by have := (natfacts q); linarith)
  have stC := lin_le5 π hπ0 (fun q => (q.1 2 : ℝ)) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (n : ℝ) 0 0 0 0 Sc S1 S1 S1 S1 S1
    (fun q => by have := (natfacts q); linarith)
  rw [E1] at stB stC
  obtain ⟨hBC2, hCC3⟩ := arith_main β (Real.sqrt n) n (lamHW β n) _ _ _ _ _ _ _ hβ hs0 hss hL
    st1 hA st2 st3 st4 st5 stB stC hCc hB0 hEb20
  refine ⟨⟨?_, ?_⟩, fun i hi => ?_⟩
  · -- part i = 1
    have := lin_le5 π hπ0 (fun q => |Real.sqrt n * (((q.1 0 : ℝ) - n) / n)|)
      (fun _ => 1) (fun q => (q.1 0 : ℝ)) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (Real.sqrt n / n * n) (-(Real.sqrt n / n)) 0 0 0
      (summ3 π hπ0 hπs (fun a _ _ => |Real.sqrt n * (((a : ℝ) - n) / n)|)) S1 Sa S1 S1 S1
      (fun q => by
        have := (natfacts q).1
        rw [abs_of_nonpos]
        · field_simp; ring_nf; nlinarith
        · apply mul_nonpos_of_nonneg_of_nonpos hs0.le
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le)
    rw [E1, hA] at this
    have e : Real.sqrt n / n * n * 1 + -(Real.sqrt n / n) * (n * lamHW β n) + 0 * 1 + 0 * 1 +
        0 * 1 = β := by
      rw [hL]
      have h2 : Real.sqrt n / n * (β * Real.sqrt n) = β := by
        rw [div_mul_eq_mul_div, div_eq_iff hN.ne']; linear_combination β * hss
      have h1 : Real.sqrt n / n * n = Real.sqrt n := div_mul_cancel₀ _ hN.ne'
      linear_combination h2
    linarith
  · have := lin_le5 π hπ0 (fun q => |Real.sqrt n * ((q.1 1 : ℝ) / n)|)
      (fun q => (q.1 1 : ℝ)) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (Real.sqrt n / n) 0 0 0 0
      (summ3 π hπ0 hπs (fun _ b _ => |Real.sqrt n * ((b : ℝ) / n)|)) Sb S1 S1 S1 S1
      (fun q => by
        rw [abs_of_nonneg (by positivity)]
        apply le_of_eq; ring)
    have e : Real.sqrt n / n * expect π (fun q => (q.1 1 : ℝ)) ≤ (4 * β ^ 2 + 6) / β := by
      calc Real.sqrt n / n * expect π (fun q => (q.1 1 : ℝ))
          ≤ Real.sqrt n / n * ((4 * β ^ 2 + 6) / β * Real.sqrt n) := by
            apply mul_le_mul_of_nonneg_left hBC2; positivity
        _ = (4 * β ^ 2 + 6) / β := by
            rw [div_mul_eq_mul_div, div_eq_iff hN.ne']
            linear_combination ((4 * β ^ 2 + 6) / β) * hss
    linarith
  · have Si : Summable (fun q : State n => π q * |(n : ℝ) * ((q.1 i : ℝ) / n)|) := by
      refine summable_bdd π hπ0 hπs _ n (fun q => ?_)
      rw [abs_abs, abs_of_nonneg (by positivity)]
      have : ((q.1 i : ℕ) : ℝ) ≤ n := by exact_mod_cast q.2.1 i
      field_simp; linarith
    have := lin_le5 π hπ0 (fun q => |(n : ℝ) * ((q.1 i : ℝ) / n)|)
      (fun q => (q.1 2 : ℝ)) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      1 0 0 0 0 Si Sc S1 S1 S1 S1
      (fun q => by
        have hi2 : q.1 i ≤ q.1 2 := q.2.2.1 hi
        have : ((q.1 i : ℕ) : ℝ) ≤ q.1 2 := by exact_mod_cast hi2
        rw [abs_of_nonneg (by positivity)]
        field_simp; linarith)
    linarith

end Main3

end JSQHalfinWhitt.Tightness

open JSQHalfinWhitt.Tightness in
theorem solution (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → β < Real.sqrt n →
      ∀ π : State n → ℝ, IsStationaryDist (genQ n (lamHW β n)) π →
        (expect π (fun q => |Real.sqrt n * (((q.1 0 : ℝ) - n) / n)|) ≤ C ∧
          expect π (fun q => |Real.sqrt n * ((q.1 1 : ℝ) / n)|) ≤ C) ∧
        ∀ i : ℕ, 2 ≤ i → expect π (fun q => |(n : ℝ) * ((q.1 i : ℝ) / n)|) ≤ C :=
  theorem_2_proof β hβ
