-- Prove2me | solution 1 for LonelyRunnerConjecture.five_runners
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-25T21:23:59.501218+00:00
-- url     : https://prove2.me/submissions/31922b76-06f4-414d-a9a5-02895980d68d

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture.FiveAux
open LonelyRunnerConjecture

/-! ### Finite certificate for the hard configuration -/

def cOf (i a b : ℕ) : ℕ := if i / 5 = 0 then 0 else if i / 5 = 1 then a else b
def digit (r q a b i : ℕ) : ℕ := ((i / 5 + 1) * q + cOf i a b + (i / 5 + 1) * (i % 5) * r) % 5
def goodB (r q a b i : ℕ) : Bool := decide (1 ≤ digit r q a b i ∧ digit r q a b i ≤ 3)

def mask (r q a b : ℕ) : ℕ :=
  (List.range 15).foldl (fun acc i => if goodB r q a b i then acc + 2 ^ i else acc) 0

def masks : List ℕ := [7629,7797,7994,8090,11687,11964,11996,12115,13678,14012,14035,14163,14571,14965,15157,15258,19702,19917,20282,20365,21870,21945,22227,22350,22905,22969,23207,23374,25846,26070,26219,26509,27001,27047,27303,27356,28907,29142,29291,29493]

theorem mask_mem : ∀ r < 4, ∀ q < 5, ∀ a < 2, ∀ e < 2,
    mask (r + 1) q a (a + e) ∈ masks := by decide +kernel

theorem triples : ∀ x ∈ masks, ∀ y ∈ masks, ∀ z ∈ masks, x &&& y &&& z ≠ 0 := by decide +kernel

theorem testBit_mask : ∀ r < 5, ∀ q < 5, ∀ a < 2, ∀ b < 3, ∀ i < 15,
    (mask r q a b).testBit i = goodB r q a b i := by decide +kernel

theorem mask_lt : ∀ r < 5, ∀ q < 5, ∀ a < 2, ∀ b < 3, mask r q a b < 2 ^ 15 := by decide +kernel

theorem pick2 : ∀ y1 y2 u1 u2 : Fin 5, ∃ a : Fin 5,
    (u1.val = 0 ∨ ((y1.val + a.val * u1.val) % 5 = 1 ∨ (y1.val + a.val * u1.val) % 5 = 2 ∨
      (y1.val + a.val * u1.val) % 5 = 3)) ∧
    (u2.val = 0 ∨ ((y2.val + a.val * u2.val) % 5 = 1 ∨ (y2.val + a.val * u2.val) % 5 = 2 ∨
      (y2.val + a.val * u2.val) % 5 = 3)) := by
  decide +kernel

lemma mem_masks (r q a b : ℕ) (h1 : 1 ≤ r) (h2 : r < 5) (h3 : q < 5) (h4 : a < 2) (h5 : a ≤ b)
    (h6 : b ≤ a + 1) : mask r q a b ∈ masks := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, b = a + e := ⟨b - a, by omega⟩
  exact mask_mem r' (by omega) q h3 a h4 e (by omega)

lemma pick3 (r1 q1 a1 b1 r2 q2 a2 b2 r3 q3 a3 b3 : ℕ)
    (hr1 : 1 ≤ r1) (hr1' : r1 < 5) (hq1 : q1 < 5) (ha1 : a1 < 2) (hb1 : a1 ≤ b1) (hb1' : b1 ≤ a1 + 1)
    (hr2 : 1 ≤ r2) (hr2' : r2 < 5) (hq2 : q2 < 5) (ha2 : a2 < 2) (hb2 : a2 ≤ b2) (hb2' : b2 ≤ a2 + 1)
    (hr3 : 1 ≤ r3) (hr3' : r3 < 5) (hq3 : q3 < 5) (ha3 : a3 < 2) (hb3 : a3 ≤ b3) (hb3' : b3 ≤ a3 + 1) :
    ∃ i < 15, goodB r1 q1 a1 b1 i = true ∧ goodB r2 q2 a2 b2 i = true ∧
      goodB r3 q3 a3 b3 i = true := by
  have hx := triples _ (mem_masks _ _ _ _ hr1 hr1' hq1 ha1 hb1 hb1') _
    (mem_masks _ _ _ _ hr2 hr2' hq2 ha2 hb2 hb2') _ (mem_masks _ _ _ _ hr3 hr3' hq3 ha3 hb3 hb3')
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hx
  rw [Nat.testBit_land, Nat.testBit_land] at hi
  simp only [Bool.and_eq_true] at hi
  obtain ⟨⟨h1, h2⟩, h3⟩ := hi
  have hi15 : i < 15 := by
    by_contra hge
    rw [not_lt] at hge
    have hlt : mask r1 q1 a1 b1 < 2 ^ i :=
      lt_of_lt_of_le (mask_lt r1 hr1' q1 hq1 a1 ha1 b1 (by omega))
        (Nat.pow_le_pow_right (by norm_num) hge)
    rw [Nat.testBit_lt_two_pow hlt] at h1
    exact absurd h1 (by simp)
  refine ⟨i, hi15, ?_, ?_, ?_⟩
  · rw [← testBit_mask r1 hr1' q1 hq1 a1 ha1 b1 (by omega) i hi15]; exact h1
  · rw [← testBit_mask r2 hr2' q2 hq2 a2 ha2 b2 (by omega) i hi15]; exact h2
  · rw [← testBit_mask r3 hr3' q3 hq3 a3 ha3 b3 (by omega) i hi15]; exact h3

/-! ### Real-number lemmas -/

lemma dist_add_int (x : ℝ) (n : ℤ) : distToNearestInt (x + n) = distToNearestInt x := by
  simp [distToNearestInt, Int.fract_add_intCast]

lemma dist_ge_of (z : ℝ) (n : ℤ) (δ : ℝ) (hz : z = n + δ) (h1 : 1/5 ≤ δ) (h2 : δ ≤ 4/5) :
    1/5 ≤ distToNearestInt z := by
  have : Int.fract z = δ := by
    rw [Int.fract_eq_iff]; exact ⟨by linarith, by linarith, n, by rw [hz]; ring⟩
  unfold distToNearestInt; rw [this]; exact le_min h1 (by linarith)

lemma unit_fifth (d : ℕ) (hd : ¬ 5 ∣ d) : 1/5 ≤ distToNearestInt ((1/5 : ℝ) * d) := by
  have h := Nat.div_add_mod d 5
  have hr : 1 ≤ d % 5 := by omega
  have hr' : d % 5 ≤ 4 := by omega
  have hrR : (1:ℝ) ≤ ((d % 5 : ℕ) : ℝ) := by exact_mod_cast hr
  have hrR' : ((d % 5 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hr'
  apply dist_ge_of _ ((d / 5 : ℕ) : ℤ) (((d % 5 : ℕ) : ℝ) / 5) _ (by linarith) (by linarith)
  have : (d:ℝ) = 5 * ((d / 5 : ℕ) : ℝ) + ((d % 5 : ℕ) : ℝ) := by exact_mod_cast h.symm
  rw [this, Int.cast_natCast]; ring

lemma lift_unit (y : ℝ) (u a : ℕ)
    (h : (⌊y⌋ + ((a * u : ℕ) : ℤ)) % 5 = 1 ∨ (⌊y⌋ + ((a * u : ℕ) : ℤ)) % 5 = 2 ∨
      (⌊y⌋ + ((a * u : ℕ) : ℤ)) % 5 = 3) :
    1/5 ≤ distToNearestInt ((y + ((a * u : ℕ) : ℝ)) / 5) := by
  obtain ⟨n, hn_def⟩ : ∃ n : ℤ, n = ⌊y⌋ + ((a * u : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hn_def] at h
  have hn : n % 5 + 5 * (n / 5) = n := by omega
  have hθ0 := Int.fract_nonneg y
  have hθ1 := Int.fract_lt_one y
  have hy := Int.floor_add_fract y
  have hρ1 : (1:ℤ) ≤ n % 5 := by omega
  have hρ3 : n % 5 ≤ 3 := by omega
  have hρ1R : (1:ℝ) ≤ ((n % 5 : ℤ) : ℝ) := by exact_mod_cast hρ1
  have hρ3R : ((n % 5 : ℤ) : ℝ) ≤ 3 := by exact_mod_cast hρ3
  have hnR : ((n % 5 : ℤ) : ℝ) + 5 * ((n / 5 : ℤ) : ℝ) = (⌊y⌋ : ℝ) + ((a * u : ℕ) : ℝ) := by
    have h1 := congrArg (Int.cast (R := ℝ)) hn
    push_cast at h1
    have h2 : (n : ℝ) = (⌊y⌋ : ℝ) + ((a * u : ℕ) : ℝ) := by rw [hn_def]; push_cast; ring
    linarith
  apply dist_ge_of _ (n / 5) ((((n % 5 : ℤ) : ℝ) + Int.fract y) / 5) _ (by linarith) (by linarith)
  linarith

/-- A unit runner in the hard configuration. -/
lemma hard_unit (u P j k : ℕ) (hP : 0 < P)
    (hd1 : 1 ≤ (j * ((u / P) % 5) + (j * (u % P)) / P + j * k * (u % 5)) % 5)
    (hd3 : (j * ((u / P) % 5) + (j * (u % P)) / P + j * k * (u % 5)) % 5 ≤ 3) :
    1/5 ≤ distToNearestInt (((j * (1 + k * P) : ℕ) : ℝ) / (5 * P) * u) := by
  set X := u / P with hX
  set q := X % 5 with hq
  set A := X / 5 with hA
  set ℓ := u % P with hℓ
  set U := u / 5 with hU
  set r := u % 5 with hr
  set c := (j * ℓ) / P with hc
  set lj := (j * ℓ) % P with hlj
  set D := j * q + c + j * k * r with hD
  set D' := D / 5 with hD'
  set dd := D % 5 with hdd
  have h1 : P * X + ℓ = u := Nat.div_add_mod u P
  have h2 : 5 * A + q = X := Nat.div_add_mod X 5
  have h3 : 5 * U + r = u := Nat.div_add_mod u 5
  have h4 : P * c + lj = j * ℓ := Nat.div_add_mod (j * ℓ) P
  have h5 : 5 * D' + dd = D := Nat.div_add_mod D 5
  have hljP : lj < P := Nat.mod_lt _ hP
  have h1R : (P:ℝ) * X + ℓ = u := by exact_mod_cast h1
  have h2R : (5:ℝ) * A + q = X := by exact_mod_cast h2
  have h3R : (5:ℝ) * U + r = u := by exact_mod_cast h3
  have h4R : (P:ℝ) * c + lj = j * ℓ := by exact_mod_cast h4
  have h5R : (5:ℝ) * D' + dd = j * q + c + j * k * r := by
    have : ((5 * D' + dd : ℕ) : ℝ) = ((j * q + c + j * k * r : ℕ) : ℝ) := by rw [h5]
    push_cast at this; exact this
  have hPR : (0:ℝ) < P := by exact_mod_cast hP
  have hljR : (lj : ℝ) < P := by exact_mod_cast hljP
  have hlj0 : (0:ℝ) ≤ lj := by positivity
  have hdd1 : (1:ℝ) ≤ dd := by exact_mod_cast hd1
  have hdd3 : (dd:ℝ) ≤ 3 := by exact_mod_cast hd3
  set N : ℕ := j * A + j * k * U + D' with hN
  have key : ((j:ℝ) * (1 + k * P)) * u = 5 * P * N + P * dd + lj := by
    rw [hN]; push_cast
    linear_combination (-(j:ℝ)) * h1R + (-(j:ℝ) * P) * h2R - h4R + (-(j:ℝ) * k * P) * h3R
      - (P:ℝ) * h5R
  have hlt : (lj:ℝ) / (5 * P) < 1/5 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hge : (0:ℝ) ≤ (lj:ℝ) / (5 * P) := by positivity
  apply dist_ge_of _ (N : ℤ) ((dd:ℝ) / 5 + (lj:ℝ) / (5 * P)) _ (by linarith) (by linarith)
  push_cast
  field_simp
  linear_combination key

/-- The runner divisible by  in the hard configuration. -/
lemma hard_v (w P' j k : ℕ) (hw : ¬ 5 ∣ w) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) (hP' : 0 < P') :
    1/5 ≤ distToNearestInt
      (((j * (1 + k * (5 * P')) : ℕ) : ℝ) / (5 * ((5 * P' : ℕ) : ℝ)) * ((5 * P' * w : ℕ) : ℝ)) := by
  have hjw : ¬ 5 ∣ j * w := by
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h with h' | h'
    · omega
    · exact hw h'
  have h := Nat.div_add_mod (j * w) 5
  have hr : 1 ≤ (j * w) % 5 := by omega
  have hr' : (j * w) % 5 ≤ 4 := by omega
  have hrR : (1:ℝ) ≤ (((j * w) % 5 : ℕ) : ℝ) := by exact_mod_cast hr
  have hrR' : (((j * w) % 5 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hr'
  have hR : (j : ℝ) * w = 5 * (((j * w) / 5 : ℕ) : ℝ) + (((j * w) % 5 : ℕ) : ℝ) := by
    have h1 := congrArg (Nat.cast (R := ℝ)) h
    push_cast at h1
    linarith
  have hPR : (0:ℝ) < P' := by exact_mod_cast hP'
  apply dist_ge_of _ ((((j * w) / 5 + j * k * P' * w : ℕ) : ℤ))
    ((((j * w) % 5 : ℕ) : ℝ) / 5) _ (by linarith) (by linarith)
  rw [Int.cast_natCast]
  push_cast
  field_simp
  linear_combination hR


/-! ### The hard configuration: three units and one multiple of 5 -/

lemma goodB_digit (u P i : ℕ) (hP : 0 < P) (hi : i < 15)
    (h : goodB (u % 5) ((u / P) % 5) ((2 * (u % P)) / P) ((3 * (u % P)) / P) i = true) :
    1 ≤ ((i / 5 + 1) * ((u / P) % 5) + ((i / 5 + 1) * (u % P)) / P +
        (i / 5 + 1) * (i % 5) * (u % 5)) % 5 ∧
      ((i / 5 + 1) * ((u / P) % 5) + ((i / 5 + 1) * (u % P)) / P +
        (i / 5 + 1) * (i % 5) * (u % 5)) % 5 ≤ 3 := by
  simp only [goodB, decide_eq_true_eq] at h
  unfold digit at h
  have hℓ : u % P < P := Nat.mod_lt _ hP
  have hc : cOf i ((2 * (u % P)) / P) ((3 * (u % P)) / P) = ((i / 5 + 1) * (u % P)) / P := by
    unfold cOf
    rcases (by omega : i / 5 = 0 ∨ i / 5 = 1 ∨ i / 5 = 2) with h0 | h0 | h0
    · rw [if_pos h0, h0, zero_add, one_mul, Nat.div_eq_of_lt hℓ]
    · rw [if_neg (by omega), if_pos h0, h0]
    · rw [if_neg (by omega), if_neg (by omega), h0]
  rw [hc] at h; exact h

lemma state_bounds (u P : ℕ) (hP : 0 < P) (hu : ¬ 5 ∣ u) :
    1 ≤ u % 5 ∧ u % 5 < 5 ∧ (u / P) % 5 < 5 ∧ (2 * (u % P)) / P < 2 ∧
      (2 * (u % P)) / P ≤ (3 * (u % P)) / P ∧ (3 * (u % P)) / P ≤ (2 * (u % P)) / P + 1 := by
  have hℓ : u % P < P := Nat.mod_lt _ hP
  refine ⟨by omega, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hP]; omega
  · exact Nat.div_le_div_right (by omega)
  · have hlt := Nat.lt_mul_div_succ (2 * (u % P)) hP
    have : (3 * (u % P)) / P < (2 * (u % P)) / P + 2 := by
      rw [Nat.div_lt_iff_lt_mul hP]; nlinarith
    omega

lemma hard (u1 u2 u3 v : ℕ) (h1 : ¬ 5 ∣ u1) (h2 : ¬ 5 ∣ u2) (h3 : ¬ 5 ∣ u3) (hv : 5 ∣ v)
    (hv0 : 0 < v) :
    ∃ t : ℝ, 1/5 ≤ distToNearestInt (t * u1) ∧ 1/5 ≤ distToNearestInt (t * u2) ∧
      1/5 ≤ distToNearestInt (t * u3) ∧ 1/5 ≤ distToNearestInt (t * v) := by
  obtain ⟨e, w, hw, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hv0.ne' 5 (by norm_num)
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; rw [pow_zero, one_mul] at hv; exact absurd hv hw
    · exact h
  have hP5 : (5 : ℕ) ^ e = 5 * 5 ^ (e - 1) := by
    rw [← pow_succ']; congr 1; omega
  set P := (5 : ℕ) ^ e with hP
  have hPpos : 0 < P := by positivity
  obtain ⟨b1, b1', b1'', b1a, b1b, b1c⟩ := state_bounds u1 P hPpos h1
  obtain ⟨b2, b2', b2'', b2a, b2b, b2c⟩ := state_bounds u2 P hPpos h2
  obtain ⟨b3, b3', b3'', b3a, b3b, b3c⟩ := state_bounds u3 P hPpos h3
  obtain ⟨i, hi, g1, g2, g3⟩ := pick3 _ _ _ _ _ _ _ _ _ _ _ _ b1 b1' b1'' b1a b1b b1c
    b2 b2' b2'' b2a b2b b2c b3 b3' b3'' b3a b3b b3c
  have hj1 : 1 ≤ i / 5 + 1 := by omega
  have hj3 : i / 5 + 1 ≤ 3 := by omega
  refine ⟨(((i / 5 + 1) * (1 + (i % 5) * P) : ℕ) : ℝ) / (5 * P), ?_, ?_, ?_, ?_⟩
  · obtain ⟨d1, d3⟩ := goodB_digit u1 P i hPpos hi g1
    exact hard_unit u1 P (i / 5 + 1) (i % 5) hPpos d1 d3
  · obtain ⟨d1, d3⟩ := goodB_digit u2 P i hPpos hi g2
    exact hard_unit u2 P (i / 5 + 1) (i % 5) hPpos d1 d3
  · obtain ⟨d1, d3⟩ := goodB_digit u3 P i hPpos hi g3
    exact hard_unit u3 P (i / 5 + 1) (i % 5) hPpos d1 d3
  · have := hard_v w (5 ^ (e - 1)) (i / 5 + 1) (i % 5) hw hj1 hj3 (by positivity)
    rw [← hP5] at this
    exact this

/-! ### Recursion on the list of speeds -/

lemma sum_div5 : ∀ V : List ℕ, 5 * (V.map (· / 5)).sum ≤ V.sum
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_div5 xs
    have := Nat.mul_div_le x 5
    omega

lemma le_sum_of_mem' : ∀ (V : List ℕ) (x : ℕ), x ∈ V → x ≤ V.sum
  | [], x, h => by simp at h
  | y :: ys, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := le_sum_of_mem' ys x h
      simp only [List.sum_cons]; omega

lemma sum_filter_le (p : ℕ → Bool) : ∀ L : List ℕ, (L.filter p).sum ≤ L.sum
  | [] => by simp
  | x :: xs => by
    have := sum_filter_le p xs
    rw [List.filter_cons]
    split <;> simp only [List.sum_cons] <;> omega

lemma cover2 : ∀ (U : List ℕ), U.length ≤ 2 → (∀ d ∈ U, ¬ 5 ∣ d) →
    ∃ u1 u2, ¬ 5 ∣ u1 ∧ ¬ 5 ∣ u2 ∧ ∀ d ∈ U, d = u1 ∨ d = u2
  | [], _, _ => ⟨1, 1, by norm_num, by norm_num, by simp⟩
  | [x], _, h => ⟨x, x, h x (by simp), h x (by simp), by simp⟩
  | [x, y], _, h => ⟨x, y, h x (by simp), h y (by simp), by simp⟩
  | _ :: _ :: _ :: _, hl, _ => by simp at hl

lemma one_elem : ∀ (V : List ℕ), V.length = 1 → ∃ v, V = [v]
  | [v], _ => ⟨v, rfl⟩
  | [], h => by simp at h
  | _ :: _ :: _, h => by simp at h

lemma unit_cond (y : ℝ) (u a : ℕ) (ha : a < 5) (hu : ¬ 5 ∣ u)
    (h : (u % 5 = 0 ∨ (((⌊y⌋ % 5).toNat + a * (u % 5)) % 5 = 1 ∨
      ((⌊y⌋ % 5).toNat + a * (u % 5)) % 5 = 2 ∨ ((⌊y⌋ % 5).toNat + a * (u % 5)) % 5 = 3))) :
    1/5 ≤ distToNearestInt ((y + ((a * u : ℕ) : ℝ)) / 5) := by
  apply lift_unit
  have hY : (((⌊y⌋ % 5).toNat : ℕ) : ℤ) = ⌊y⌋ % 5 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hm : (a * u) % 5 = (a * (u % 5)) % 5 := by
    rw [Nat.mul_mod, Nat.mul_mod a (u % 5), Nat.mod_mod]
  obtain ⟨M, hM⟩ : ∃ M, M = a * u := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = a * (u % 5) := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = (⌊y⌋ % 5).toNat := ⟨_, rfl⟩
  rw [← hM, ← hZ] at hm
  rw [← hZ, ← hYdef] at h
  rw [← hYdef] at hY
  rw [← hM]
  rcases h with h0 | h0
  · omega
  · omega

theorem main : ∀ n : ℕ, ∀ L : List ℕ, L.sum ≤ n → L.length ≤ 4 → (∀ d ∈ L, 0 < d) →
    ∃ t : ℝ, ∀ d ∈ L, 1/5 ≤ distToNearestInt (t * d) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hsum hlen hpos
  have hsplit0 := List.length_eq_length_filter_add (l := L) (fun d => decide (5 ∣ d))
  set V := L.filter (fun d => decide (5 ∣ d)) with hV
  set U := L.filter (fun d => !decide (5 ∣ d)) with hU
  have hsplit : L.length = V.length + U.length := hsplit0
  have hmem : ∀ d ∈ L, (¬ 5 ∣ d ∧ d ∈ U) ∨ (5 ∣ d ∧ d ∈ V) := by
    intro d hd
    by_cases h : 5 ∣ d
    · right; exact ⟨h, List.mem_filter.mpr ⟨hd, by simp [h]⟩⟩
    · left; exact ⟨h, List.mem_filter.mpr ⟨hd, by simp [h]⟩⟩
  have hUu : ∀ d ∈ U, ¬ 5 ∣ d := by
    intro d hd; have := (List.mem_filter.mp hd).2; simpa using this
  have hVv : ∀ d ∈ V, 5 ∣ d ∧ 0 < d := by
    intro d hd
    obtain ⟨hdL, h⟩ := List.mem_filter.mp hd
    exact ⟨by simpa using h, hpos d hdL⟩
  by_cases hVe : V = []
  · refine ⟨1/5, fun d hd => ?_⟩
    rcases hmem d hd with ⟨h, -⟩ | ⟨-, h⟩
    · exact unit_fifth d h
    · rw [hVe] at h; simp at h
  by_cases hUl : U.length ≤ 2
  · set V' := V.map (· / 5) with hV'
    have hVsum : 0 < V.sum := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil V hVe
      have := le_sum_of_mem' V x hx
      have := (hVv x hx).2
      omega
    have hVL : V.sum ≤ L.sum := sum_filter_le _ L
    have h5 : 5 * V'.sum ≤ V.sum := sum_div5 V
    have hlt : V'.sum < n := by omega
    have hV'len : V'.length ≤ 4 := by
      rw [hV', List.length_map]; omega
    have hV'pos : ∀ d ∈ V', 0 < d := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      obtain ⟨h5x, hx0⟩ := hVv x hx
      omega
    obtain ⟨t', ht'⟩ := ih V'.sum hlt V' le_rfl hV'len hV'pos
    obtain ⟨u1, u2, hu1, hu2, hcov⟩ := cover2 U hUl hUu
    have hY1 : (⌊t' * u1⌋ % 5).toNat < 5 := by
      have := Int.toNat_of_nonneg (Int.emod_nonneg ⌊t' * u1⌋ (by norm_num : (5:ℤ) ≠ 0))
      omega
    have hY2 : (⌊t' * u2⌋ % 5).toNat < 5 := by
      have := Int.toNat_of_nonneg (Int.emod_nonneg ⌊t' * u2⌋ (by norm_num : (5:ℤ) ≠ 0))
      omega
    obtain ⟨a, ha1, ha2⟩ := pick2 ⟨_, hY1⟩ ⟨_, hY2⟩ ⟨u1 % 5, Nat.mod_lt _ (by norm_num)⟩
      ⟨u2 % 5, Nat.mod_lt _ (by norm_num)⟩
    refine ⟨(t' + (a.val : ℝ)) / 5, fun d hd => ?_⟩
    rcases hmem d hd with ⟨hd5, hdU⟩ | ⟨hd5, hdV⟩
    · rcases hcov d hdU with rfl | rfl
      · rw [show (t' + (a.val:ℝ)) / 5 * (d:ℝ) = (t' * d + ((a.val * d : ℕ) : ℝ)) / 5 by
          push_cast; ring]
        exact unit_cond _ d a.val a.isLt hd5 ha1
      · rw [show (t' + (a.val:ℝ)) / 5 * (d:ℝ) = (t' * d + ((a.val * d : ℕ) : ℝ)) / 5 by
          push_cast; ring]
        exact unit_cond _ d a.val a.isLt hd5 ha2
    · obtain ⟨d', rfl⟩ := hd5
      have hd'V' : d' ∈ V' := List.mem_map.mpr ⟨5 * d', hdV, by omega⟩
      have h := ht' d' hd'V'
      rw [show (t' + (a.val:ℝ)) / 5 * ((5 * d' : ℕ) : ℝ) = t' * d' + (((a.val * d' : ℕ) : ℤ) : ℝ) by
        push_cast; ring, dist_add_int]
      exact h
  · have hVpos : 0 < V.length := List.length_pos_of_ne_nil hVe
    have hUlen : U.length = 3 := by omega
    have hVlen : V.length = 1 := by omega
    obtain ⟨u1, u2, u3, hU3⟩ := List.length_eq_three.mp hUlen
    obtain ⟨v, hV1⟩ := one_elem V hVlen
    have hu1 := hUu u1 (by rw [hU3]; simp)
    have hu2 := hUu u2 (by rw [hU3]; simp)
    have hu3 := hUu u3 (by rw [hU3]; simp)
    obtain ⟨hv5, hv0⟩ := hVv v (by rw [hV1]; simp)
    obtain ⟨t, ht1, ht2, ht3, htv⟩ := hard u1 u2 u3 v hu1 hu2 hu3 hv5 hv0
    refine ⟨t, fun d hd => ?_⟩
    rcases hmem d hd with ⟨-, hdU⟩ | ⟨-, hdV⟩
    · rw [hU3] at hdU
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hdU
      rcases hdU with rfl | rfl | rfl
      · exact ht1
      · exact ht2
      · exact ht3
    · rw [hV1, List.mem_singleton] at hdV
      subst hdV; exact htv

theorem lrc_four : LRC 4 := by
  intro S hS hpos
  obtain ⟨t, ht⟩ := main S.toList.sum S.toList le_rfl (by rw [Finset.length_toList, hS])
    (fun d hd => hpos d (Finset.mem_toList.mp hd))
  refine ⟨t, fun v hv => ?_⟩
  have hk : (1 : ℝ) / ((4 : ℕ) + 1 : ℝ) = 1 / 5 := by norm_num
  rw [hk]
  exact ht v (Finset.mem_toList.mpr hv)

end LonelyRunnerConjecture.FiveAux

theorem solution : LonelyRunnerConjecture.LRC 4 :=
  LonelyRunnerConjecture.FiveAux.lrc_four
