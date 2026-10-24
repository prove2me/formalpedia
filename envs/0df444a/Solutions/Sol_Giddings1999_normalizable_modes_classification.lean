-- Prove2me | solution 1 for Giddings1999.normalizable_modes_classification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:09:11.884554+00:00
-- url     : https://prove2.me/submissions/83351a7d-276c-4ca6-b3a0-18180960d248

import Mathlib
import Definitions.Def_Giddings1999_AdSModes
section

open Filter Topology Set

namespace NN104

/-- power series `∑ c n z^n` -/
noncomputable def ser (c : ℕ → ℝ) (z : ℝ) : ℝ := ∑' n, c n * z ^ n

/-- derivative coefficients -/
def dc (c : ℕ → ℝ) : ℕ → ℝ := fun n => ((n : ℝ) + 1) * c (n + 1)

/-- polynomially bounded coefficients -/
def PB (c : ℕ → ℝ) : Prop := ∃ M : ℝ, 0 ≤ M ∧ ∃ k : ℕ, ∀ n, |c n| ≤ M * ((n : ℝ) + 1) ^ k

lemma PB.dc {c : ℕ → ℝ} (h : PB c) : PB (dc c) := by
  obtain ⟨M, hM, k, hk⟩ := h
  refine ⟨M * 2 ^ k, by positivity, k + 1, fun n => ?_⟩
  have h1 := hk (n + 1)
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have h2 : (((n + 1 : ℕ) : ℝ) + 1) ^ k ≤ 2 ^ k * ((n : ℝ) + 1) ^ k := by
    rw [← mul_pow]; push_cast
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  simp only [NN104.dc, abs_mul]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1), pow_succ]
  calc ((n:ℝ) + 1) * |c (n + 1)| ≤ ((n:ℝ) + 1) * (M * (2 ^ k * ((n : ℝ) + 1) ^ k)) := by
        gcongr; exact h1.trans (by gcongr)
    _ = M * 2 ^ k * (((n:ℝ) + 1) ^ k * ((n:ℝ) + 1)) := by ring

lemma summable_poly_geom (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k
    (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr)
  have hg : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((h.add hg).mul_left (2 ^ k))
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have : ((n : ℝ) + 1) ^ k ≤ 2 ^ k * ((n:ℝ) ^ k + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [Nat.cast_zero, zero_add, one_pow]
      have h0 : (0:ℝ) ≤ (0:ℝ) ^ k := by positivity
      nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]
    · have h1 : (1:ℝ) ≤ n := by exact_mod_cast hpos
      calc ((n : ℝ) + 1) ^ k ≤ (2 * n) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
        _ = 2 ^ k * (n:ℝ) ^ k := by rw [mul_pow]
        _ ≤ 2 ^ k * ((n:ℝ) ^ k + 1) := by nlinarith [pow_pos (two_pos (α := ℝ)) k]
  calc ((n : ℝ) + 1) ^ k * r ^ n ≤ 2 ^ k * ((n:ℝ) ^ k + 1) * r ^ n := by gcongr
    _ = 2 ^ k * ((n:ℝ) ^ k * r ^ n + r ^ n) := by ring

lemma PB.summable_abs {c : ℕ → ℝ} (h : PB c) {z : ℝ} (hz : |z| < 1) :
    Summable (fun n => |c n| * |z| ^ n) := by
  obtain ⟨M, hM, k, hk⟩ := h
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_poly_geom k (abs_nonneg z) hz).mul_left M)
  rw [← mul_assoc]; gcongr; exact hk n

lemma PB.summable {c : ℕ → ℝ} (h : PB c) {z : ℝ} (hz : |z| < 1) :
    Summable (fun n => c n * z ^ n) := by
  refine Summable.of_norm_bounded (h.summable_abs hz) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]

lemma hasDerivAt_ser {c : ℕ → ℝ} (h : PB c) {z : ℝ} (hz : |z| < 1) :
    HasDerivAt (ser c) (ser (dc c) z) z := by
  obtain ⟨ρ, hzρ, hρ1⟩ := exists_between hz
  have hρ0 : 0 ≤ ρ := (abs_nonneg z).trans hzρ.le
  let u : ℕ → ℝ := fun n => |c n| * ((n:ℝ) * ρ ^ (n - 1))
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    have := h.dc.summable_abs (z := ρ) (by rw [abs_of_nonneg hρ0]; exact hρ1)
    refine this.congr fun n => ?_
    simp only [u, NN104.dc, abs_mul, abs_of_nonneg hρ0, Nat.add_sub_cancel]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)]; push_cast; ring
  have hmem : z ∈ Ioo (-ρ) ρ := by
    constructor <;> linarith [neg_abs_le z, le_abs_self z]
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun n y => c n * y ^ n)
    (g' := fun n y => c n * ((n:ℝ) * y ^ (n - 1))) hu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hasDerivAt_pow n y).const_mul (c n))
    (fun n y hy => by
      simp only [u, Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
      gcongr
      exact abs_le.2 ⟨by linarith [hy.1], hy.2.le⟩)
    hmem (h.summable hz) hmem
  refine key.congr_deriv ?_
  have hs : Summable (fun n => c n * ((n:ℝ) * z ^ (n - 1))) := by
    rw [← summable_nat_add_iff 1]
    refine (h.dc.summable hz).congr fun n => ?_
    simp only [NN104.dc, Nat.add_sub_cancel]; push_cast; ring
  rw [hs.tsum_eq_zero_add]
  simp only [ser, NN104.dc, Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
  congr 1; funext n; push_cast; ring

lemma contDiffOn_ser : ∀ (n : ℕ) {c : ℕ → ℝ}, PB c → ContDiffOn ℝ n (ser c) (Ioo (-1) 1)
  | 0, c, h => by
    simp only [Nat.cast_zero, contDiffOn_zero]
    intro z hz
    exact (hasDerivAt_ser h (abs_lt.2 hz)).continuousAt.continuousWithinAt
  | n + 1, c, h => by
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun z hz => (hasDerivAt_ser h (abs_lt.2 hz)).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    refine (contDiffOn_ser n h.dc).congr fun z hz => ?_
    exact (hasDerivAt_ser h (abs_lt.2 hz)).deriv

/-- shift: `z * ser c z = ser (sh c) z` -/
def sh (c : ℕ → ℝ) : ℕ → ℝ := fun n => Nat.casesOn n 0 c

lemma PB.sh {c : ℕ → ℝ} (h : PB c) : PB (sh c) := by
  obtain ⟨M, hM, k, hk⟩ := h
  refine ⟨M, hM, k, fun n => ?_⟩
  cases n with
  | zero => simp [NN104.sh]; positivity
  | succ n =>
    simp only [NN104.sh]
    refine (hk n).trans ?_
    gcongr; push_cast; linarith

lemma mul_ser {c : ℕ → ℝ} (h : PB c) {z : ℝ} (hz : |z| < 1) : z * ser c z = ser (sh c) z := by
  rw [ser, ser, (h.sh.summable hz).tsum_eq_zero_add, ← tsum_mul_left]
  show _ = 0 * z ^ 0 + ∑' n, c n * z ^ (n+1)
  rw [zero_mul, zero_add]
  exact tsum_congr fun n => by ring

/-- the hypergeometric equation for a series whose coefficients satisfy the recursion -/
lemma hyp_ode {c : ℕ → ℝ} (h : PB c) (A B C : ℝ)
    (hrec : ∀ n : ℕ, ((n:ℝ) + 1) * ((n:ℝ) + C) * c (n + 1) = ((n:ℝ) + A) * ((n:ℝ) + B) * c n)
    {z : ℝ} (hz : |z| < 1) :
    z * (1 - z) * ser (dc (dc c)) z + (C - (A + B + 1) * z) * ser (dc c) z
      - A * B * ser c z = 0 := by
  have e1 : z * (1 - z) * ser (dc (dc c)) z + (C - (A + B + 1) * z) * ser (dc c) z
      - A * B * ser c z = ser (sh (dc (dc c))) z - ser (sh (sh (dc (dc c)))) z
        + C * ser (dc c) z - (A + B + 1) * ser (sh (dc c)) z - A * B * ser c z := by
    rw [← mul_ser h.dc.dc hz, ← mul_ser h.dc.dc.sh hz, ← mul_ser h.dc.dc hz, ← mul_ser h.dc hz]
    ring
  rw [e1]
  simp only [ser]
  have H := ((((h.dc.dc.sh.summable hz).hasSum.sub (h.dc.dc.sh.sh.summable hz).hasSum).add
      ((h.dc.summable hz).hasSum.mul_left C)).sub
      ((h.dc.sh.summable hz).hasSum.mul_left (A + B + 1))).sub ((h.summable hz).hasSum.mul_left (A * B))
  refine H.unique ?_
  convert hasSum_zero using 1
  funext n
  rcases n with _ | _ | n
  · simp [NN104.sh, NN104.dc]
    have := hrec 0; simp at this; linarith
  · simp [NN104.sh, NN104.dc]
    have := hrec 1; push_cast at this; ring_nf; ring_nf at this; linear_combination z * this
  · simp only [NN104.sh, NN104.dc]
    have := hrec (n + 2)
    push_cast at this ⊢
    linear_combination z ^ (n + 2) * this

end NN104

end

section

open Filter Topology Finset

namespace NN104

/-- hypergeometric coefficients `(A)_n (B)_n / ((C)_n n!)` -/
noncomputable def tc (A B C : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => tc A B C n * ((A + n) * (B + n)) / ((C + n) * (n + 1))

lemma tc_rec (A B C : ℝ) (hC : 0 < C) (n : ℕ) :
    ((n:ℝ) + 1) * ((n:ℝ) + C) * tc A B C (n + 1) = ((n:ℝ) + A) * ((n:ℝ) + B) * tc A B C n := by
  simp only [tc]
  have : (C + n) * ((n:ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

lemma tc_succ (A B C : ℝ) (n : ℕ) :
    tc A B C (n + 1) = tc A B C n * ((A + n) * (B + n)) / ((C + n) * (n + 1)) := rfl

lemma tc_summable (A B C : ℝ) (hC : 0 < C) (hν : 0 < C - A - B) :
    Summable (fun n => |tc A B C n|) ∧
      Tendsto (fun n : ℕ => (n:ℝ) * |tc A B C n|) atTop (𝓝 0) := by
  set ν := C - A - B with hνdef
  set u : ℕ → ℝ := fun n => |tc A B C n| with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => abs_nonneg _
  obtain ⟨N0, hN0⟩ := exists_nat_ge (|A| + |B| + 2 * |A * B| / ν + C + 1)
  have hq : 0 ≤ 2 * |A * B| / ν := by positivity
  have hstep : ∀ n : ℕ, N0 ≤ n →
      u (n + 1) * ((C + n) * (n + 1)) = u n * ((A + n) * (B + n)) := by
    intro n hn
    have hn' : (N0 : ℝ) ≤ n := by exact_mod_cast hn
    have hA : 0 < A + n := by linarith [neg_abs_le A, abs_nonneg B]
    have hB : 0 < B + n := by linarith [neg_abs_le B, abs_nonneg A]
    have hY : 0 < (C + n) * ((n:ℝ) + 1) := by positivity
    simp only [hu, tc, abs_div, abs_mul, abs_of_pos hA, abs_of_pos hB, abs_of_pos hY]
    field_simp
  let D : ℕ → ℝ := fun n => (n:ℝ) * u n
  have hD0 : ∀ n, 0 ≤ D n := fun n => mul_nonneg n.cast_nonneg (hu0 n)
  have hD : ∀ n : ℕ, N0 ≤ n → ν / 4 * u n ≤ D n - D (n + 1) := by
    intro n hn
    have hn' : (N0 : ℝ) ≤ n := by exact_mod_cast hn
    have hCn : 0 < C + n := by positivity
    have e : (D n - D (n + 1)) * (C + n) = u n * (ν * n - A * B) := by
      have := hstep n hn
      simp only [D]; push_cast
      linear_combination (-1 : ℝ) * this
    have hAB : ν * (C + n) / 4 ≤ ν * n - A * B := by
      have h1 : 2 * |A * B| / ν ≤ n := by linarith [abs_nonneg A, abs_nonneg B]
      have h2 : 2 * |A * B| ≤ ν * n := by
        rw [div_le_iff₀ hν] at h1; linarith
      have h3 : C ≤ n := by linarith [abs_nonneg A, abs_nonneg B]
      nlinarith [le_abs_self (A * B)]
    have : ν / 4 * u n * (C + n) ≤ (D n - D (n + 1)) * (C + n) := by
      rw [e]; nlinarith [hu0 n]
    exact le_of_mul_le_mul_right this hCn
  have hpart : ∀ N : ℕ, N0 ≤ N →
      ∑ n ∈ range N, u n + 4 / ν * D N ≤ ∑ n ∈ range N0, u n + 4 / ν * D N0 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact le_rfl
    | succ N hN ih =>
      rw [sum_range_succ]
      have := hD N hN
      have h4 : u N ≤ 4 / ν * (D N - D (N + 1)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hν]; linarith
      linarith
  set K := ∑ n ∈ range N0, u n + 4 / ν * D N0
  have hsum : Summable u := by
    refine summable_of_sum_range_le hu0 (c := K) fun N => ?_
    rcases le_or_gt N0 N with h | h
    · have := hpart N h
      have : 0 ≤ 4 / ν * D N := by have := hD0 N; positivity
      linarith
    · have : ∑ n ∈ range N, u n ≤ ∑ n ∈ range N0, u n :=
        sum_le_sum_of_subset_of_nonneg (range_mono h.le) fun i _ _ => hu0 i
      have : 0 ≤ 4 / ν * D N0 := by have := hD0 N0; positivity
      simp only [K]; linarith
  refine ⟨hsum, ?_⟩
  -- the limit of `D`
  let D' : ℕ → ℝ := fun k => D (k + N0)
  have hanti : Antitone D' := by
    refine antitone_nat_of_succ_le fun k => ?_
    have := hD (k + N0) (by omega)
    have : 0 ≤ ν / 4 * u (k + N0) := by have := hu0 (k + N0); positivity
    simp only [D', show k + 1 + N0 = k + N0 + 1 by omega]
    linarith
  have hbdd : BddBelow (Set.range D') := ⟨0, by rintro _ ⟨k, rfl⟩; exact hD0 _⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ k, D' k
  have hL0 : 0 ≤ L := le_ciInf fun k => hD0 _
  have hL : L = 0 := by
    by_contra hne
    have hLp : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
    have hN0pos : 0 < N0 := by
      have : (1 : ℝ) ≤ N0 := by linarith [abs_nonneg A, abs_nonneg B]
      exact_mod_cast (show (0:ℝ) < N0 by linarith)
    have hs1 : Summable (fun k : ℕ => u (k + N0)) := (summable_nat_add_iff N0).2 hsum
    have hs2 : Summable (fun k : ℕ => L * (1 / ((k + N0 : ℕ) : ℝ))) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs1
      have hk : (0:ℝ) < ((k + N0 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k + N0 by omega)
      have := ciInf_le hbdd k
      simp only [D', D] at this
      rw [mul_one_div, div_le_iff₀ hk]
      linarith [mul_comm (((k + N0 : ℕ) : ℝ)) (u (k + N0))]
    have hs3 : Summable (fun k : ℕ => 1 / ((k + N0 : ℕ) : ℝ)) := by
      have := hs2.mul_left (1 / L)
      refine this.congr fun k => ?_
      field_simp
    rw [summable_nat_add_iff N0 (f := fun n : ℕ => 1 / (n : ℝ))] at hs3
    exact Real.not_summable_one_div_natCast hs3
  rw [hL] at hlim
  exact (tendsto_add_atTop_iff_nat N0).1 hlim

lemma tc_shift (A B C : ℝ) (hC : 0 < C) (n : ℕ) :
    tc A B (C + 1) n * (C + n) = C * tc A B C n := by
  induction n with
  | zero => simp [tc]
  | succ n ih =>
    simp only [tc]
    have h1 : (C + 1 + n) * ((n:ℝ) + 1) ≠ 0 := by positivity
    have h2 : (C + n) * ((n:ℝ) + 1) ≠ 0 := by positivity
    have h3 : (C + n) ≠ 0 := by positivity
    rw [show C * (tc A B C n * ((A + n) * (B + n)) / ((C + n) * (n + 1)))
      = (C * tc A B C n) * ((A + n) * (B + n)) / ((C + n) * (n + 1)) by ring, ← ih]
    push_cast
    field_simp
    ring

lemma contig (A B C : ℝ) (hC : 0 < C) (hν : 0 < C - A - B) :
    C * (C - A - B) * ∑' n, tc A B C n = (C - A) * (C - B) * ∑' n, tc A B (C + 1) n := by
  have hC1 : 0 < C + 1 := by linarith
  have hν1 : 0 < C + 1 - A - B := by linarith
  obtain ⟨ht, hlim⟩ := tc_summable A B C hC hν
  have hs := (tc_summable A B (C + 1) hC1 hν1).1
  have hT := (ht.of_abs).hasSum
  have hS := (hs.of_abs).hasSum
  have hpart : ∀ N : ℕ, ∑ n ∈ range N, (C * (C - A - B) * tc A B C n
      - (C - A) * (C - B) * tc A B (C + 1) n) = -(C * ((N:ℝ) * tc A B C N)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih]
      have e1 := tc_shift A B C hC N
      have e2 := tc_rec A B (C + 1) hC1 N
      have e3 := tc_shift A B C hC (N + 1)
      push_cast at e3 ⊢
      linear_combination ((N:ℝ) - C + A + B) * e1 - ((N:ℝ) + 1) * e3 + e2
  have h1 := ((hT.mul_left (C * (C - A - B))).sub (hS.mul_left ((C - A) * (C - B)))).tendsto_sum_nat
  simp_rw [hpart] at h1
  have h2 : Tendsto (fun N : ℕ => -(C * ((N:ℝ) * tc A B C N))) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => (N:ℝ) * tc A B C N) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine hlim.congr fun N => ?_
      simp [Function.comp, abs_mul]
    simpa using (this.const_mul C).neg
  have := tendsto_nhds_unique h1 h2
  linarith

lemma tc_zero (A B C : ℝ) : tc A B C 0 = 1 := rfl

attribute [irreducible] tc

end NN104

end

section

open Filter Topology Finset

namespace NN104

lemma aux (a b c x y y' : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ c * b) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 < y) (hyy : y ≤ y') : a * x / y' ≤ c * (b * x / y) := by
  have hy' : 0 < y' := hy.trans_le hyy
  calc a * x / y' ≤ c * b * x / y' := by gcongr
    _ ≤ c * b * x / y := div_le_div_of_nonneg_left (by positivity) hy hyy
    _ = c * (b * x / y) := by ring


lemma tc_le (A B C C' : ℝ) (hC : 0 < C) (hCC : C ≤ C') (n : ℕ) :
    |tc A B C' (n + 1)| ≤ C / C' * |tc A B C (n + 1)| := by
  have hC' : 0 < C' := hC.trans_le hCC
  induction n with
  | zero =>
    rw [tc_succ, tc_succ, tc_zero, tc_zero]
    simp only [abs_div, abs_mul, Nat.cast_zero, add_zero, one_mul, zero_add, mul_one]
    rw [abs_of_pos hC, abs_of_pos hC']
    field_simp
    try exact le_rfl
  | succ n ih =>
    rw [tc_succ A B C' (n + 1), tc_succ A B C (n + 1)]
    have h1 : 0 < (C' + ((n + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ) + 1) := by positivity
    have h2 : 0 < (C + ((n + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ) + 1) := by positivity
    simp only [abs_div, abs_mul, abs_of_pos h1, abs_of_pos h2]
    have hle : (C + ((n + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ) + 1) ≤
        (C' + ((n + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ) + 1) := by gcongr
    exact aux _ _ _ _ _ _ (abs_nonneg _) ih (by positivity) (abs_nonneg _) (by positivity) h2 hle

lemma F_near_one (A B C C' : ℝ) (hC : 0 < C) (hν : 0 < C - A - B) (hCC : C ≤ C') :
    |∑' n, tc A B C' n - 1| ≤ C / C' * ∑' n, |tc A B C n| := by
  have hC' : 0 < C' := hC.trans_le hCC
  have hsC := (tc_summable A B C hC hν).1
  have hsC' := (tc_summable A B C' hC' (by linarith)).1
  rw [hsC'.of_abs.tsum_eq_zero_add, tc_zero, add_sub_cancel_left]
  have hs1 : Summable (fun n => |tc A B C (n + 1)|) := (summable_nat_add_iff 1).2 hsC
  calc |∑' n, tc A B C' (n + 1)| ≤ ∑' n, |tc A B C' (n + 1)| := by
        have hs2 : Summable (fun n => ‖tc A B C' (n + 1)‖) := by
          simpa only [Real.norm_eq_abs] using (summable_nat_add_iff 1).2 hsC'
        have := norm_tsum_le_tsum_norm hs2
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' n, C / C' * |tc A B C (n + 1)| :=
        Summable.tsum_le_tsum (fun n => tc_le A B C C' hC hCC n) ((summable_nat_add_iff 1).2 hsC')
          (hs1.mul_left _)
    _ = C / C' * ∑' n, |tc A B C (n + 1)| := tsum_mul_left
    _ ≤ C / C' * ∑' n, |tc A B C n| := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hsC.tsum_eq_zero_add]
        linarith [abs_nonneg (tc A B C 0)]

/-- Gauss: `₂F₁(A, B; C; 1) ≠ 0` when `C - A - B > 0` and `C - A`, `C - B` are not
nonpositive integers. -/
lemma F_ne_zero (A B C : ℝ) (hC : 0 < C) (hν : 0 < C - A - B)
    (hA : ∀ k : ℕ, C + k - A ≠ 0) (hB : ∀ k : ℕ, C + k - B ≠ 0) :
    ∑' n, tc A B C n ≠ 0 := by
  intro h0
  have hall : ∀ k : ℕ, ∑' n, tc A B (C + k) n = 0 := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      have hc := contig A B (C + k) (by positivity) (by linarith [k.cast_nonneg (α := ℝ)])
      rw [ih, mul_zero] at hc
      have hne : (C + k - A) * (C + k - B) ≠ 0 := mul_ne_zero (hA k) (hB k)
      push_cast
      rw [← add_assoc]
      exact (mul_eq_zero.1 hc.symm).resolve_left hne
  set S := ∑' n, |tc A B C n|
  obtain ⟨N, hN⟩ := exists_nat_gt (C * S)
  have h := F_near_one A B C (C + N) hC hν (by linarith [N.cast_nonneg (α := ℝ)])
  rw [hall N, zero_sub, abs_neg, abs_one] at h
  have hpos : 0 < C + N := by positivity
  have : C / (C + N) * S < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hpos]; linarith
  linarith

end NN104

end

section

open Real Filter Topology Set
open Giddings1999

namespace NN104

lemma pow_pred_mul (l : ℕ) (s : ℝ) : (l:ℝ) * s^(l-1) * s = l * s^l := by
  cases l with
  | zero => simp
  | succ k => simp [pow_succ]; ring

lemma cos2_mem {r : ℝ} (hr : r ∈ Ioo 0 (π / 2)) : cos (2 * r) ∈ Ioo (-1) 1 := by
  have h1 : 0 < 2 * r := by linarith [hr.1]
  have h2 : 2 * r < π := by linarith [hr.2]
  have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
  have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2, pi_pos])
  rw [cos_two_mul]
  constructor
  · nlinarith
  · nlinarith [sin_sq_add_cos_sq r]

section
variable (P P1 P2 : ℝ → ℝ)
  (hP : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt P (P1 x) x)
  (hP1 : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt P1 (P2 x) x)
include hP

lemma hasDerivAt_chiG (l : ℕ) (b r : ℝ) (hr : r ∈ Ioo 0 (π / 2)) :
    HasDerivAt (fun r => sin r ^ l * cos r ^ b * P (cos (2 * r)))
      (sin r ^ l * cos r ^ b * ((l * cos r / sin r - b * sin r / cos r) * P (cos (2*r))
        + (-4 * sin r * cos r) * P1 (cos (2*r)))) r := by
  have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2, pi_pos])
  have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
  have h1 : HasDerivAt (fun r => sin r ^ l) (l * sin r ^ (l-1) * cos r) r :=
    (hasDerivAt_sin r).fun_pow l
  have h2 : HasDerivAt (fun r => cos r ^ b) (b * cos r ^ (b - 1) * (-sin r)) r := by
    have := (hasDerivAt_cos r).rpow_const (p := b) (Or.inl hc.ne')
    refine this.congr_deriv ?_; ring
  have h3 : HasDerivAt (fun r => P (cos (2 * r)))
      (P1 (cos (2*r)) * (-sin (2*r) * 2)) r := by
    have hc2 : HasDerivAt (fun r => cos (2 * r)) (-sin (2*r) * 2) r := by
      have := ((hasDerivAt_id r).const_mul 2).cos
      simpa using this
    exact (hP _ (cos2_mem hr)).comp r hc2
  have := (h1.fun_mul h2).fun_mul h3
  refine this.congr_deriv ?_
  rw [rpow_sub_one hc.ne', sin_two_mul]
  have e := pow_pred_mul l (sin r)
  field_simp
  linear_combination (cos r ^ 2 * P (cos (2 * r))) * e

include hP1 in
lemma hasDerivAt_DG (l : ℕ) (b r : ℝ) (hr : r ∈ Ioo 0 (π / 2)) :
    HasDerivAt (fun r => sin r ^ l * cos r ^ b * ((l * cos r / sin r - b * sin r / cos r) * P (cos (2*r))
        + (-4 * sin r * cos r) * P1 (cos (2*r))))
      (sin r ^ l * cos r ^ b * (((l * cos r / sin r - b * sin r / cos r)^2 + (-l / sin r^2 - b / cos r^2))
          * P (cos (2*r))
        + (2 * (l * cos r / sin r - b * sin r / cos r) * (-4 * sin r * cos r) + (-4 * (cos r^2 - sin r^2)))
          * P1 (cos (2*r))
        + (-4 * sin r * cos r)^2 * P2 (cos (2*r)))) r := by
  have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2, pi_pos])
  have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
  have h1 : HasDerivAt (fun r => sin r ^ l) (l * sin r ^ (l-1) * cos r) r :=
    (hasDerivAt_sin r).fun_pow l
  have h2 : HasDerivAt (fun r => cos r ^ b) (b * cos r ^ (b - 1) * (-sin r)) r := by
    have := (hasDerivAt_cos r).rpow_const (p := b) (Or.inl hc.ne')
    refine this.congr_deriv ?_; ring
  have hX : HasDerivAt (fun r => cos (2 * r)) (-4 * sin r * cos r) r := by
    have := ((hasDerivAt_id r).const_mul 2).cos
    refine (by simpa using this : HasDerivAt (fun r => cos (2 * r)) (-sin (2*r) * 2) r).congr_deriv ?_
    rw [sin_two_mul]; ring
  have hPX := (hP _ (cos2_mem hr)).comp r hX
  have hP1X := (hP1 _ (cos2_mem hr)).comp r hX
  have hg : HasDerivAt (fun r => l * cos r / sin r - b * sin r / cos r) (-l / sin r^2 - b / cos r^2) r := by
    have := (((hasDerivAt_cos r).const_mul (l:ℝ)).div (hasDerivAt_sin r) hs.ne').fun_sub
      (((hasDerivAt_sin r).const_mul b).div (hasDerivAt_cos r) hc.ne')
    refine this.congr_deriv ?_
    have py := sin_sq_add_cos_sq r
    field_simp
    linear_combination (-(l:ℝ) * cos r ^ 2 - b * sin r ^ 2) * py
  have hh : HasDerivAt (fun r => -4 * sin r * cos r) (-4 * (cos r^2 - sin r^2)) r := by
    have := ((hasDerivAt_sin r).const_mul (-4:ℝ)).fun_mul (hasDerivAt_cos r)
    refine this.congr_deriv ?_; ring
  have h0 : HasDerivAt (fun r => sin r ^ l * cos r ^ b)
      (sin r ^ l * cos r ^ b * (l * cos r / sin r - b * sin r / cos r)) r := by
    have := h1.fun_mul h2
    refine this.congr_deriv ?_
    rw [rpow_sub_one hc.ne']
    have e := pow_pred_mul l (sin r)
    field_simp
    linear_combination (cos r ^ 2) * e
  have := h0.fun_mul ((hg.fun_mul hPX).fun_add (hh.fun_mul hP1X))
  refine this.congr_deriv ?_
  simp only [Function.comp]
  ring

include hP1 in
/-- generalized radial reduction: a solution `P` of the Jacobi-type equation on `(-1, 1)` gives
a radial solution `sin^l r cos^b r P(cos 2r)`. -/
lemma radialG (d : ℕ) (m R ω : ℝ) (l : ℕ) (b : ℝ) (hM : m ^ 2 * R ^ 2 = b * (b - d))
    (hcd : ContDiffOn ℝ 2 P (Ioo (-1) 1))
    (hjac : ∀ x ∈ Ioo (-1 : ℝ) 1, (1 - x^2) * P2 x
      + ((b - d/2) - ((l:ℝ) + d/2 - 1) - (((l:ℝ) + d/2 - 1) + (b - d/2) + 2) * x) * P1 x
      + (ω ^ 2 - (b + l) ^ 2) / 4 * P x = 0) :
    IsRadialSolution d m R ω l (fun r => sin r ^ l * cos r ^ b * P (cos (2 * r))) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    apply ContDiffAt.contDiffWithinAt
    refine ((contDiff_sin.pow l).contDiffAt.mul ?_).mul ?_
    · exact (contDiffAt_rpow_const_of_ne hc.ne').comp r contDiff_cos.contDiffAt
    · have hm := cos2_mem hr
      have : ContDiffAt ℝ 2 P (cos (2 * r)) := hcd.contDiffAt (Ioo_mem_nhds hm.1 hm.2)
      exact this.comp r (contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffAt
  · intro r hr
    have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2, pi_pos])
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    have hev : deriv (fun r => sin r ^ l * cos r ^ b * P (cos (2 * r))) =ᶠ[𝓝 r]
        (fun r => sin r ^ l * cos r ^ b * ((l * cos r / sin r - b * sin r / cos r) * P (cos (2*r))
          + (-4 * sin r * cos r) * P1 (cos (2*r)))) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
      exact (hasDerivAt_chiG P P1 hP l b r' hr').deriv
    rw [hev.deriv_eq, (hasDerivAt_chiG P P1 hP l b r hr).deriv,
      (hasDerivAt_DG P P1 P2 hP hP1 l b r hr).deriv]
    have jac := hjac (cos (2*r)) (cos2_mem hr)
    rw [cos_two_mul] at jac
    beta_reduce
    rw [cos_two_mul, hM]
    have py := sin_sq_add_cos_sq r
    set S := sin r
    set C := cos r
    set χ0 := S ^ l * C ^ b
    set Q0 := P (2 * C ^ 2 - 1)
    set Q1 := P1 (2 * C ^ 2 - 1)
    set Q2 := P2 (2 * C ^ 2 - 1)
    have ecP : (l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2) + ((d:ℝ) - 1) / (S * C) * (l * C / S - b * S / C)
        + ω^2 - l * (l + d - 2) / S^2 - b * (b - d) / C^2 = ω ^ 2 - (b + l) ^ 2 := by
      have e1 : (l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2) + ((d:ℝ) - 1) / (S * C) * (l * C / S - b * S / C)
          - l * (l + d - 2) / S^2 - b * (b - d) / C^2
          = (l^2 * C^2 - l^2) / S^2 + (b^2 * S^2 - b^2) / C^2 - 2 * l * b := by
        field_simp; ring
      have e2 : ((l:ℝ)^2 * C^2 - l^2) / S^2 = -l^2 := by
        rw [div_eq_iff (by positivity)]; linear_combination (l:ℝ)^2 * py
      have e3 : (b^2 * S^2 - b^2) / C^2 = -b^2 := by
        rw [div_eq_iff (by positivity)]; linear_combination b^2 * py
      linear_combination e1 + e2 + e3
    have ecP1 : 2 * (l * C / S - b * S / C) * (-4 * S * C) + (-4 * (C^2 - S^2))
        + ((d:ℝ) - 1) / (S * C) * (-4 * S * C) = 4 * ((b - d/2) - ((l:ℝ) + d/2 - 1)
          - (((l:ℝ) + d/2 - 1) + (b - d/2) + 2) * (2 * C ^ 2 - 1)) := by
      have e1 : 2 * (l * C / S - b * S / C) * (-4 * S * C) = -8 * l * C^2 + 8 * b * S^2 := by
        field_simp; ring
      have e2 : ((d:ℝ) - 1) / (S * C) * (-4 * S * C) = -4 * ((d:ℝ) - 1) := by
        field_simp
      rw [e1, e2]; linear_combination (8 * b + 4) * py
    have eh : (-4 * S * C)^2 = 4 * (1 - (2 * C ^ 2 - 1) ^ 2) := by
      linear_combination (16 * C^2) * py
    have key : χ0 * (((l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2)) * Q0
          + (2 * (l * C / S - b * S / C) * (-4 * S * C) + (-4 * (C^2 - S^2))) * Q1
          + (-4 * S * C)^2 * Q2)
        + ((d:ℝ) - 1) / (S * C) * (χ0 * ((l * C / S - b * S / C) * Q0 + (-4 * S * C) * Q1))
        + ω^2 * (χ0 * Q0) - l * (l + d - 2) / S^2 * (χ0 * Q0) - b * (b - d) / C^2 * (χ0 * Q0)
        = χ0 * (((l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2) + ((d:ℝ) - 1) / (S * C) * (l * C / S - b * S / C)
        + ω^2 - l * (l + d - 2) / S^2 - b * (b - d) / C^2) * Q0
          + (2 * (l * C / S - b * S / C) * (-4 * S * C) + (-4 * (C^2 - S^2))
        + ((d:ℝ) - 1) / (S * C) * (-4 * S * C)) * Q1 + (-4 * S * C)^2 * Q2) := by ring
    rw [key, ecP, ecP1, eh]
    linear_combination (4 * χ0) * jac

end

end NN104

end

section

open Real Filter Topology Set
open Giddings1999

namespace NN104

theorem main (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R) (ω : ℝ) (l : ℕ)
    (hω : ∀ n : ℕ, |ω| ≠ omegaNL d m R n l) :
    ∃ χ : ℝ → ℝ, IsRadialSolution d m R ω l χ ∧ IsRegularAtOrigin χ ∧
      Tendsto (fun r => χ r / cos r ^ twoHMinus d m R) (𝓝[<] (π / 2)) (𝓝 1) ∧
      ∃ L : ℝ, L ≠ 0 ∧ Tendsto (fun r => χ r / sin r ^ l) (𝓝[>] 0) (𝓝 L) := by
  set ν := nu d m R with hνdef
  set b := twoHMinus d m R with hbdef
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hsq : Real.sqrt ((d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2) ^ 2 = (d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hνge : (d:ℝ) / 2 ≤ ν := by
    have : (d:ℝ) ≤ Real.sqrt ((d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (m * R)])
    simp only [hνdef, nu]; linarith
  have hb : b = d / 2 - ν := rfl
  have hb0 : b ≤ 0 := by linarith
  have hM : m ^ 2 * R ^ 2 = b * (b - d) := by
    rw [hb]; simp only [hνdef, nu]; nlinarith [hsq]
  set A := (b + l - ω) / 2 with hA
  set B := (b + l + ω) / 2 with hB
  set Cc : ℝ := l + d / 2 with hCc
  have hCpos : 0 < Cc := by positivity
  have hνpos : 0 < Cc - A - B := by rw [hA, hB, hCc, hb]; linarith
  have hAk : ∀ k : ℕ, Cc + k - A ≠ 0 := by
    intro k h
    apply hω k
    have : ω = -omegaNL d m R k l := by
      simp only [omegaNL, twoHPlus, hCc, hA, hb] at h ⊢; linarith
    have hpos : 0 < omegaNL d m R k l := by
      simp only [omegaNL, twoHPlus]
      have := k.cast_nonneg (α := ℝ); have := l.cast_nonneg (α := ℝ); linarith
    rw [this, abs_neg, abs_of_pos hpos]
  have hBk : ∀ k : ℕ, Cc + k - B ≠ 0 := by
    intro k h
    apply hω k
    have : ω = omegaNL d m R k l := by
      simp only [omegaNL, twoHPlus, hCc, hB, hb] at h ⊢; linarith
    have hpos : 0 < omegaNL d m R k l := by
      simp only [omegaNL, twoHPlus]
      have := k.cast_nonneg (α := ℝ); have := l.cast_nonneg (α := ℝ); linarith
    rw [this, abs_of_pos hpos]
  set F1 := ∑' n, tc A B Cc n with hF1
  have hF1ne : F1 ≠ 0 := F_ne_zero A B Cc hCpos hνpos hAk hBk
  obtain ⟨hsum, -⟩ := tc_summable A B Cc hCpos hνpos
  set c : ℕ → ℝ := fun n => tc A B Cc n / F1 with hc
  set S := ∑' n, |tc A B Cc n|
  have hcsum : Summable (fun n => |c n|) := by
    simp only [hc, abs_div]; exact hsum.div_const _
  have hPB : PB c := by
    refine ⟨S / |F1|, by positivity, 0, fun n => ?_⟩
    simp only [hc, abs_div, pow_zero, mul_one]
    gcongr
    exact hsum.le_tsum n (fun j _ => abs_nonneg _)
  have hrec : ∀ n : ℕ, ((n:ℝ) + 1) * ((n:ℝ) + Cc) * c (n + 1) = ((n:ℝ) + A) * ((n:ℝ) + B) * c n := by
    intro n
    have := tc_rec A B Cc hCpos n
    simp only [hc]
    field_simp
    linear_combination this
  -- the functions in the Jacobi variable `x = cos 2r = 1 - 2z`
  let P : ℝ → ℝ := fun x => ser c ((1 - x) / 2)
  let P1 : ℝ → ℝ := fun x => -(1/2) * ser (dc c) ((1 - x) / 2)
  let P2 : ℝ → ℝ := fun x => 1/4 * ser (dc (dc c)) ((1 - x) / 2)
  have hzm : ∀ x ∈ Ioo (-1 : ℝ) 1, |(1 - x) / 2| < 1 := by
    intro x hx; rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
  have hlin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 - x) / 2) (-(1/2)) x := by
    intro x
    have := ((hasDerivAt_id x).const_sub 1).div_const 2
    exact this.congr_deriv (by norm_num)
  have hP : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt P (P1 x) x := by
    intro x hx
    have h := (hasDerivAt_ser hPB (hzm x hx)).comp x (hlin x)
    exact h.congr_deriv (by simp only [P1]; ring)
  have hP1 : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt P1 (P2 x) x := by
    intro x hx
    have := ((hasDerivAt_ser hPB.dc (hzm x hx)).comp x (hlin x)).const_mul (-(1/2) : ℝ)
    refine this.congr_deriv ?_
    simp only [P2]; ring
  have hcd : ContDiffOn ℝ 2 P (Ioo (-1) 1) := by
    have h1 := contDiffOn_ser 2 hPB
    have h2 : ContDiff ℝ 2 (fun x : ℝ => (1 - x) / 2) := by fun_prop
    refine h1.comp h2.contDiffOn ?_
    intro x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hjac : ∀ x ∈ Ioo (-1 : ℝ) 1, (1 - x^2) * P2 x
      + ((b - d/2) - ((l:ℝ) + d/2 - 1) - (((l:ℝ) + d/2 - 1) + (b - d/2) + 2) * x) * P1 x
      + (ω ^ 2 - (b + l) ^ 2) / 4 * P x = 0 := by
    intro x hx
    have hode := hyp_ode hPB A B Cc hrec (hzm x hx)
    simp only [P, P1, P2]
    rw [hA, hB, hCc] at hode
    linear_combination hode
  have hrad := radialG P P1 P2 hP hP1 d m R ω l b hM hcd hjac
  -- the `z`-form of the mode
  have hPz : ∀ r, P (cos (2 * r)) = ser c (sin r ^ 2) := by
    intro r; simp only [P]; congr 1; rw [cos_two_mul, cos_sq']; ring
  have hbound : ∀ z ∈ Icc (0:ℝ) 1, |ser c z| ≤ ∑' n, |c n| := by
    intro z hz
    have hs : Summable (fun n => ‖c n * z ^ n‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hcsum
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hz.1]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hz.1 hz.2)
    calc |ser c z| = ‖∑' n, c n * z ^ n‖ := rfl
      _ ≤ ∑' n, ‖c n * z ^ n‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n, |c n| := by
        refine Summable.tsum_le_tsum (fun n => ?_) hs hcsum
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hz.1]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hz.1 hz.2)
  have hcont : ContinuousOn (ser c) (Icc 0 1) := by
    refine continuousOn_tsum (u := fun n => |c n|) (fun n => by fun_prop) hcsum fun n z hz => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hz.1]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hz.1 hz.2)
  refine ⟨fun r => sin r ^ l * cos r ^ b * P (cos (2 * r)), hrad, ?_, ?_, ?_⟩
  · -- regular at the origin
    refine ⟨(1/2 : ℝ) ^ b * ∑' n, |c n|, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    have hr0 : 0 < r := hr.1
    have hr1 : r ≤ π / 4 := hr.2
    have hcr : 1/2 ≤ cos r := by
      rw [← cos_pi_div_three]
      exact cos_le_cos_of_nonneg_of_le_pi hr0.le (by linarith [pi_pos]) (by linarith [pi_pos])
    have hcpos : 0 < cos r := by linarith
    simp only
    rw [hPz, abs_mul, abs_mul, abs_pow, abs_of_pos (rpow_pos_of_pos hcpos b)]
    have h1 : |sin r| ^ l ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_sin_le_one r)
    have h2 : cos r ^ b ≤ (1/2 : ℝ) ^ b := rpow_le_rpow_of_nonpos (by norm_num) hcr hb0
    have h3 := hbound (sin r ^ 2) ⟨sq_nonneg _, by rw [sin_sq]; linarith [sq_nonneg (cos r)]⟩
    have h4 : 0 ≤ cos r ^ b := (rpow_pos_of_pos hcpos b).le
    calc |sin r| ^ l * cos r ^ b * |ser c (sin r ^ 2)| ≤ 1 * (1/2 : ℝ) ^ b * ∑' n, |c n| := by
          gcongr
      _ = _ := by ring
  · -- boundary behaviour
    have hser1 : ser c 1 = 1 := by
      simp only [ser, one_pow, mul_one, hc]
      rw [tsum_div_const, div_self hF1ne]
    have hsin : Tendsto (fun r => sin r ^ 2) (𝓝[<] (π / 2)) (𝓝[Icc 0 1] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun r =>
        ⟨sq_nonneg _, by rw [sin_sq]; linarith [sq_nonneg (cos r)]⟩⟩
      have : Tendsto (fun r => sin r ^ 2) (𝓝 (π / 2)) (𝓝 (sin (π / 2) ^ 2)) :=
        ((continuous_sin.pow 2).tendsto _)
      rw [sin_pi_div_two, one_pow] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun r => ser c (sin r ^ 2)) (𝓝[<] (π / 2)) (𝓝 1) := by
      have := ((hcont 1 ⟨by norm_num, le_rfl⟩).tendsto).comp hsin
      rw [hser1] at this
      exact this
    have h2 : Tendsto (fun r => sin r ^ l) (𝓝[<] (π / 2)) (𝓝 1) := by
      have : Tendsto (fun r => sin r ^ l) (𝓝 (π / 2)) (𝓝 (sin (π / 2) ^ l)) :=
        ((continuous_sin.pow l).tendsto _)
      rw [sin_pi_div_two, one_pow] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 := h2.mul h1
    rw [mul_one] at h3
    refine h3.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < π / 2 by positivity)] with r hr
    have hcpos : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    have hne : cos r ^ b ≠ 0 := (rpow_pos_of_pos hcpos b).ne'
    beta_reduce
    rw [hPz]
    field_simp
  · -- behaviour at the origin
    refine ⟨c 0, by simp only [hc, tc_zero]; exact one_div_ne_zero hF1ne, ?_⟩
    have hser0 : ser c 0 = c 0 := by
      simp only [ser]
      rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, mul_zero])]
      simp
    have hsin : Tendsto (fun r => sin r ^ 2) (𝓝[>] 0) (𝓝[Icc 0 1] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun r =>
        ⟨sq_nonneg _, by rw [sin_sq]; linarith [sq_nonneg (cos r)]⟩⟩
      have : Tendsto (fun r => sin r ^ 2) (𝓝 0) (𝓝 (sin 0 ^ 2)) :=
        ((continuous_sin.pow 2).tendsto _)
      rw [sin_zero, zero_pow two_ne_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun r => ser c (sin r ^ 2)) (𝓝[>] 0) (𝓝 (c 0)) := by
      have := ((hcont 0 ⟨le_rfl, by norm_num⟩).tendsto).comp hsin
      rw [hser0] at this
      exact this
    have h2 : Tendsto (fun r => cos r ^ b) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun r => cos r ^ b) (𝓝 0) (𝓝 (cos 0 ^ b)) :=
        ((Real.continuousAt_rpow_const _ _ (Or.inl (by rw [cos_zero]; norm_num))).comp
          continuous_cos.continuousAt)
      rw [cos_zero, one_rpow] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 := h2.mul h1
    rw [one_mul] at h3
    refine h3.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < π / 2 by positivity)] with r hr
    have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2, pi_pos])
    have hne : sin r ^ l ≠ 0 := (pow_pos hs l).ne'
    beta_reduce
    rw [hPz]
    field_simp

end NN104

end

section

open Real Filter Topology Set
open Giddings1999

namespace NN104U

variable {d : ℕ} {m R ω : ℝ} {l : ℕ}

lemma mem_aux {r : ℝ} (hr : r ∈ Ioo 0 (π / 2)) : 0 < sin r ∧ 0 < cos r :=
  ⟨sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2, pi_pos]),
   cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩⟩

lemma sol_diff {χ : ℝ → ℝ} (h : IsRadialSolution d m R ω l χ) {r : ℝ} (hr : r ∈ Ioo 0 (π / 2)) :
    HasDerivAt χ (deriv χ r) r ∧ HasDerivAt (deriv χ) (deriv (deriv χ) r) r := by
  have h2 : ContDiffOn ℝ (1 + 1) χ (Ioo 0 (π / 2)) := by
    have := h.1; norm_num at this ⊢; exact this
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] at h2
  have hU := Ioo_mem_nhds hr.1 hr.2
  refine ⟨(h2.1.differentiableAt hU).hasDerivAt, ?_⟩
  exact ((h2.2.2.differentiableOn one_ne_zero).differentiableAt hU).hasDerivAt

lemma sol_ode {χ : ℝ → ℝ} (h : IsRadialSolution d m R ω l χ) {r : ℝ} (hr : r ∈ Ioo 0 (π / 2)) :
    deriv (deriv χ) r = -(((d:ℝ) - 1) / (sin r * cos r)) * deriv χ r
      - (ω ^ 2 - (l : ℝ) * ((l : ℝ) + d - 2) / sin r ^ 2 - m ^ 2 * R ^ 2 / cos r ^ 2) * χ r := by
  linear_combination h.2 r hr

lemma sol_lin {χ1 χ2 : ℝ → ℝ} (h1 : IsRadialSolution d m R ω l χ1)
    (h2 : IsRadialSolution d m R ω l χ2) (a c : ℝ) :
    IsRadialSolution d m R ω l (fun r => a * χ1 r + c * χ2 r) := by
  refine ⟨(contDiffOn_const.mul h1.1).add (contDiffOn_const.mul h2.1), fun r hr => ?_⟩
  have hd1 : ∀ r ∈ Ioo 0 (π / 2), deriv (fun r => a * χ1 r + c * χ2 r) r
      = a * deriv χ1 r + c * deriv χ2 r := by
    intro r hr
    exact (((sol_diff h1 hr).1.const_mul a).add ((sol_diff h2 hr).1.const_mul c)).deriv
  have hev : deriv (fun r => a * χ1 r + c * χ2 r) =ᶠ[𝓝 r]
      (fun r => a * deriv χ1 r + c * deriv χ2 r) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr' using hd1 r' hr'
  rw [hev.deriv_eq, hd1 r hr,
    (((sol_diff h1 hr).2.const_mul a).fun_add ((sol_diff h2 hr).2.const_mul c)).deriv]
  beta_reduce
  linear_combination a * h1.2 r hr + c * h2.2 r hr

lemma sol_congr {χ1 χ2 : ℝ → ℝ} (h1 : IsRadialSolution d m R ω l χ1)
    (heq : EqOn χ2 χ1 (Ioo 0 (π / 2))) : IsRadialSolution d m R ω l χ2 := by
  have hd : ∀ r ∈ Ioo 0 (π / 2), deriv χ2 r = deriv χ1 r := fun r hr =>
    (heq.eventuallyEq_of_mem (Ioo_mem_nhds hr.1 hr.2)).deriv_eq
  refine ⟨h1.1.congr heq, fun r hr => ?_⟩
  have hev : deriv χ2 =ᶠ[𝓝 r] deriv χ1 := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr' using hd r' hr'
  rw [hev.deriv_eq, hd r hr, heq hr]
  exact h1.2 r hr

lemma sol_neg_ω {χ : ℝ → ℝ} :
    IsRadialSolution d m R (-ω) l χ ↔ IsRadialSolution d m R ω l χ := by
  simp only [IsRadialSolution, neg_sq]

lemma wronskian {χ1 χ2 : ℝ → ℝ} (h1 : IsRadialSolution d m R ω l χ1)
    (h2 : IsRadialSolution d m R ω l χ2) (hd : 2 ≤ d) :
    ∃ K, ∀ r ∈ Ioo 0 (π / 2),
      (χ1 r * deriv χ2 r - deriv χ1 r * χ2 r) * (sin r / cos r) ^ (d - 1) = K := by
  obtain ⟨k, hk⟩ : ∃ k, d - 1 = k + 1 := ⟨d - 2, by omega⟩
  have hkd : ((k + 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [← hk, Nat.cast_sub (by omega)]; simp
  rw [hk]
  set Φ := fun r => (χ1 r * deriv χ2 r - deriv χ1 r * χ2 r) * (sin r / cos r) ^ (k + 1)
  have hΦ : ∀ r ∈ Ioo 0 (π / 2), HasDerivAt Φ 0 r := by
    intro r hr
    obtain ⟨hs, hc⟩ := mem_aux hr
    obtain ⟨a1, b1⟩ := sol_diff h1 hr
    obtain ⟨a2, b2⟩ := sol_diff h2 hr
    have ht : HasDerivAt (fun r => sin r / cos r) (1 / cos r ^ 2) r := by
      have := (hasDerivAt_sin r).div (hasDerivAt_cos r) hc.ne'
      refine this.congr_deriv ?_
      have py := sin_sq_add_cos_sq r
      field_simp
      linear_combination py
    have hW : HasDerivAt (fun r => χ1 r * deriv χ2 r - deriv χ1 r * χ2 r)
        (χ1 r * deriv (deriv χ2) r - deriv (deriv χ1) r * χ2 r) r := by
      refine ((a1.mul b2).sub (b1.mul a2)).congr_deriv ?_; ring
    have := hW.fun_mul (ht.fun_pow (k + 1))
    refine this.congr_deriv ?_
    rw [sol_ode h1 hr, sol_ode h2 hr, ← hkd]
    simp only [Nat.add_sub_cancel]
    have e : (sin r / cos r) ^ (k + 1) * (1 / (sin r * cos r)) = (sin r / cos r) ^ k * (1 / cos r ^ 2) := by
      rw [pow_succ]; field_simp
    linear_combination (-(((k + 1 : ℕ) : ℝ)) * (χ1 r * deriv χ2 r - deriv χ1 r * χ2 r)) * e
  obtain ⟨K, hK⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr => (hΦ r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hΦ r hr).deriv)
  exact ⟨K, hK⟩

/-- uniqueness: a solution vanishing near `0` vanishes identically (energy estimate). -/
lemma vanish {ψ : ℝ → ℝ} (h : IsRadialSolution d m R ω l ψ) (hd : 1 ≤ d) {r0 : ℝ} (hr0 : 0 < r0)
    (hr0' : r0 < π / 2) (hz : ∀ r ∈ Ioo 0 r0, ψ r = 0) : ∀ r ∈ Ioo 0 (π / 2), ψ r = 0 := by
  intro t ht
  by_cases hts : t < r0
  · exact hz t ⟨ht.1, hts⟩
  push_neg at hts
  set a := r0 / 2 with ha_def
  have ha0 : 0 < a := by positivity
  have hat : a < t := by linarith
  have hψa : ψ a = 0 := hz a ⟨ha0, by linarith⟩
  have hψ'a : deriv ψ a = 0 := by
    have : ψ =ᶠ[𝓝 a] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds ha0 (show a < r0 by linarith)] with x hx using hz x hx
    rw [this.deriv_eq]; simp
  have hsub : ∀ s ∈ Icc a t, s ∈ Ioo 0 (π / 2) := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩
  have hsa : 0 < sin a := (mem_aux (hsub a ⟨le_rfl, hat.le⟩)).1
  have hct : 0 < cos t := (mem_aux ht).2
  set Q0 := ω ^ 2 + |(l : ℝ) * ((l : ℝ) + d - 2)| / sin a ^ 2 + m ^ 2 * R ^ 2 / cos t ^ 2 with hQ0
  set L := 1 + Q0
  have hq : ∀ s ∈ Icc a t,
      |ω ^ 2 - (l : ℝ) * ((l : ℝ) + d - 2) / sin s ^ 2 - m ^ 2 * R ^ 2 / cos s ^ 2| ≤ Q0 := by
    intro s hs
    obtain ⟨hss, hcs⟩ := mem_aux (hsub s hs)
    have h1 : sin a ≤ sin s := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos])
      (by linarith [(hsub s hs).2]) hs.1
    have h2 : cos t ≤ cos s := cos_le_cos_of_nonneg_of_le_pi (by linarith [hs.1]) (by linarith [ht.2, pi_pos]) hs.2
    have e1 : |(l : ℝ) * ((l : ℝ) + d - 2)| / sin s ^ 2 ≤ |(l : ℝ) * ((l : ℝ) + d - 2)| / sin a ^ 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (pow_le_pow_left₀ hsa.le h1 2)
    have e2 : m ^ 2 * R ^ 2 / cos s ^ 2 ≤ m ^ 2 * R ^ 2 / cos t ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hct.le h2 2)
    have e3 : |(l : ℝ) * ((l : ℝ) + d - 2) / sin s ^ 2| = |(l : ℝ) * ((l : ℝ) + d - 2)| / sin s ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < sin s ^ 2)]
    have e4 : 0 ≤ m ^ 2 * R ^ 2 / cos s ^ 2 := by positivity
    calc |ω ^ 2 - (l : ℝ) * ((l : ℝ) + d - 2) / sin s ^ 2 - m ^ 2 * R ^ 2 / cos s ^ 2|
        ≤ |ω ^ 2| + |(l : ℝ) * ((l : ℝ) + d - 2) / sin s ^ 2| + |m ^ 2 * R ^ 2 / cos s ^ 2| := by
          have := abs_sub (ω ^ 2 - (l : ℝ) * ((l : ℝ) + d - 2) / sin s ^ 2) (m ^ 2 * R ^ 2 / cos s ^ 2)
          have := abs_sub (ω ^ 2) ((l : ℝ) * ((l : ℝ) + d - 2) / sin s ^ 2)
          linarith
      _ ≤ Q0 := by
          rw [abs_of_nonneg (sq_nonneg ω), e3, abs_of_nonneg e4]; linarith
  have hQ0 : 0 ≤ Q0 := (abs_nonneg _).trans (hq a ⟨le_rfl, hat.le⟩)
  let E : ℝ → ℝ := fun s => (ψ s ^ 2 + deriv ψ s ^ 2) * exp (-(L * s))
  have hE : ∀ s ∈ Icc a t, HasDerivAt E
      ((2 * ψ s * deriv ψ s + 2 * deriv ψ s * deriv (deriv ψ) s) * exp (-(L * s))
        + (ψ s ^ 2 + deriv ψ s ^ 2) * (exp (-(L * s)) * (-L))) s := by
    intro s hs
    obtain ⟨a1, b1⟩ := sol_diff h (hsub s hs)
    have hexp : HasDerivAt (fun s => exp (-(L * s))) (exp (-(L * s)) * (-L)) s := by
      have := ((hasDerivAt_id s).const_mul L).neg.exp
      simpa using this
    have := ((a1.fun_pow 2).fun_add (b1.fun_pow 2)).fun_mul hexp
    refine this.congr_deriv ?_
    first | ring | (simp; ring) | simp
  have hanti : AntitoneOn E (Icc a t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a t) ?_ ?_ ?_
    · exact fun s hs => (hE s hs).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun s hs => (hE s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      have hs' := Ioo_subset_Icc_self hs
      rw [(hE s hs').deriv, sol_ode h (hsub s hs')]
      obtain ⟨hss, hcs⟩ := mem_aux (hsub s hs')
      set X := ψ s
      set Y := deriv ψ s
      set q := ω ^ 2 - (l : ℝ) * ((l : ℝ) + d - 2) / sin s ^ 2 - m ^ 2 * R ^ 2 / cos s ^ 2
      have hp : 0 ≤ ((d:ℝ) - 1) / (sin s * cos s) := by
        have : (1:ℝ) ≤ d := by exact_mod_cast hd
        have : 0 ≤ (d:ℝ) - 1 := by linarith
        positivity
      have hqs : |q| ≤ Q0 := hq s hs'
      have h1 : 2 * X * Y * (1 - q) ≤ (X ^ 2 + Y ^ 2) * (1 + Q0) := by
        have a1 : |2 * X * Y| ≤ X ^ 2 + Y ^ 2 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (X + Y), sq_nonneg (X - Y)]
        have a2 : |1 - q| ≤ 1 + Q0 := by
          have := abs_sub (1:ℝ) q; rw [abs_one] at this; linarith
        calc 2 * X * Y * (1 - q) ≤ |2 * X * Y * (1 - q)| := le_abs_self _
          _ = |2 * X * Y| * |1 - q| := abs_mul _ _
          _ ≤ (X ^ 2 + Y ^ 2) * (1 + Q0) := mul_le_mul a1 a2 (abs_nonneg _) (by positivity)
      have h2 : 0 ≤ ((d:ℝ) - 1) / (sin s * cos s) * Y ^ 2 := mul_nonneg hp (sq_nonneg Y)
      have he := exp_pos (-(L * s))
      have h3 : 2 * X * Y + 2 * Y * (-(((d:ℝ) - 1) / (sin s * cos s)) * Y - q * X)
          - L * (X ^ 2 + Y ^ 2) ≤ 0 := by
        simp only [L]; nlinarith [h1, h2]
      have key := mul_le_mul_of_nonneg_left h3 he.le
      rw [mul_zero] at key
      linarith [key]
  have h1 := hanti ⟨le_rfl, hat.le⟩ ⟨hat.le, le_rfl⟩ hat.le
  simp only [E, hψa, hψ'a] at h1
  have he := exp_pos (-(L * t))
  have h2 : ψ t ^ 2 ≤ 0 := by nlinarith [sq_nonneg (ψ t), sq_nonneg (deriv ψ t)]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h2 (sq_nonneg _))

lemma pow_inv_bound (κ : ℝ) (hκ : 0 < κ) (l : ℕ) :
    ∃ φ : ℝ → ℝ, (∀ r, 0 < r → HasDerivAt φ (-κ / r ^ (2 * l + 1)) r) ∧
      Tendsto (fun r => φ r * sin r ^ l) (𝓝[>] 0) atTop := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · refine ⟨fun r => -κ * log r, fun r hr => ?_, ?_⟩
    · have := (hasDerivAt_log hr.ne').const_mul (-κ)
      refine this.congr_deriv ?_; field_simp; first | norm_num | simp | ring
    · simp only [pow_zero, mul_one]
      exact tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg (by linarith)
  · obtain ⟨j, hj⟩ : ∃ j, 2 * l = j + 1 := ⟨2 * l - 1, by omega⟩
    refine ⟨fun r => κ / (j + 1) * (r ^ (j + 1))⁻¹, fun r hr => ?_, ?_⟩
    · have := ((hasDerivAt_pow (j + 1) r).inv (pow_ne_zero _ hr.ne')).const_mul (κ / (j + 1))
      refine this.congr_deriv ?_
      rw [hj]; push_cast
      field_simp
      ring
    · -- lower bound by `κ/(j+1) (2/π)^l (r^l)⁻¹`
      have hmain : Tendsto (fun r : ℝ => κ / (j + 1) * (2 / π) ^ l * (r ^ l)⁻¹) (𝓝[>] 0) atTop := by
        have hpow : Tendsto (fun r : ℝ => r ^ l) (𝓝[>] 0) (𝓝[>] 0) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
          · have : Tendsto (fun r : ℝ => r ^ l) (𝓝 0) (𝓝 (0 ^ l)) := (continuous_pow l).tendsto 0
            rw [zero_pow hl.ne'] at this
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with r hr using pow_pos (show (0:ℝ) < r from hr) l
        exact (tendsto_inv_nhdsGT_zero.comp hpow).const_mul_atTop
          (mul_pos (div_pos hκ (by positivity)) (by positivity))
      refine tendsto_atTop_mono' _ ?_ hmain
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < π / 2 by positivity)] with r hr
      have h1 : 2 / π * r ≤ sin r := mul_le_sin hr.1.le hr.2.le
      have hr0 := hr.1
      have h2 : (2 / π * r) ^ l ≤ sin r ^ l := pow_le_pow_left₀ (by positivity) h1 l
      have e : (r ^ (j + 1))⁻¹ = ((r ^ l)⁻¹) ^ 2 := by
        rw [← hj, inv_pow (r ^ l), ← pow_mul, mul_comm l 2]
      rw [e, mul_pow] at *
      calc κ / (j + 1) * (2 / π) ^ l * (r ^ l)⁻¹
          = κ / (j + 1) * ((r ^ l)⁻¹ ^ 2) * ((2 / π) ^ l * r ^ l) := by
            field_simp
        _ ≤ κ / (j + 1) * ((r ^ l)⁻¹ ^ 2) * sin r ^ l := by gcongr

lemma blowup {χ1 χ2 : ℝ → ℝ} (h1 : IsRadialSolution d m R ω l χ1)
    (h2 : IsRadialSolution d m R ω l χ2) (hd : 2 ≤ d) (hreg : IsRegularAtOrigin χ1)
    {r1 L K : ℝ} (hr1 : 0 < r1) (hr1' : r1 ≤ π / 4) (hL : 0 < L)
    (hlow : ∀ r ∈ Ioo 0 r1, L / 2 * sin r ^ l ≤ χ2 r) (hup : ∀ r ∈ Ioo 0 r1, χ2 r ≤ 2 * L * sin r ^ l)
    (hK : 0 < K)
    (hW : ∀ r ∈ Ioo 0 (π / 2),
      (χ1 r * deriv χ2 r - deriv χ1 r * χ2 r) * (sin r / cos r) ^ (d - 1) = K) : False := by
  obtain ⟨B, hB⟩ := hreg
  have hIoo : ∀ r ∈ Ioo 0 r1, r ∈ Ioo 0 (π / 2) := fun r hr => ⟨hr.1, by linarith [hr.2, pi_pos]⟩
  have hB' : ∀ r ∈ Ioo 0 r1, χ1 r ≤ B := fun r hr =>
    (le_abs_self _).trans (hB ⟨r, ⟨hr.1, by linarith [hr.2]⟩, rfl⟩)
  have hχpos : ∀ r ∈ Ioo 0 r1, 0 < χ2 r := fun r hr =>
    lt_of_lt_of_le (by have := (mem_aux (hIoo r hr)).1; positivity) (hlow r hr)
  set κ := K / (2 ^ (d - 1) * (4 * L ^ 2)) with hκ
  have hκpos : 0 < κ := by positivity
  have hQ : ∀ r ∈ Ioo 0 r1, HasDerivAt (fun r => χ1 r / χ2 r)
      ((deriv χ1 r * χ2 r - χ1 r * deriv χ2 r) / χ2 r ^ 2) r := fun r hr =>
    (sol_diff h1 (hIoo r hr)).1.div (sol_diff h2 (hIoo r hr)).1 (hχpos r hr).ne'
  have hQ' : ∀ r ∈ Ioo 0 r1,
      (deriv χ1 r * χ2 r - χ1 r * deriv χ2 r) / χ2 r ^ 2 ≤ -κ / r ^ (2 * l + 1) := by
    intro r hr
    obtain ⟨hs, hc⟩ := mem_aux (hIoo r hr)
    have hpos := hχpos r hr
    have hc2 : 1 / 2 ≤ cos r := by
      rw [← cos_pi_div_three]
      exact cos_le_cos_of_nonneg_of_le_pi hr.1.le (by linarith [pi_pos]) (by linarith [pi_pos, hr.2])
    have hsr : sin r ≤ r := (sin_lt hr.1).le
    have hs1 : sin r ≤ 1 := sin_le_one r
    have htb : sin r / cos r ≤ 2 * sin r := by
      rw [div_le_iff₀ hc]; nlinarith
    obtain ⟨k, hk⟩ : ∃ k, d - 1 = k + 1 := ⟨d - 2, by omega⟩
    have ht : (sin r / cos r) ^ (d - 1) ≤ 2 ^ (d - 1) * sin r := by
      calc (sin r / cos r) ^ (d - 1) ≤ (2 * sin r) ^ (d - 1) :=
            pow_le_pow_left₀ (by positivity) htb _
        _ = 2 ^ (d - 1) * (sin r ^ k * sin r) := by rw [mul_pow, hk]; ring
        _ ≤ 2 ^ (d - 1) * (1 * sin r) := by
            gcongr; exact pow_le_one₀ hs.le hs1
        _ = 2 ^ (d - 1) * sin r := by ring
    have hχ : χ2 r ^ 2 ≤ 4 * L ^ 2 * sin r ^ (2 * l) := by
      have := hup r hr
      have := pow_le_pow_left₀ hpos.le this 2
      calc χ2 r ^ 2 ≤ (2 * L * sin r ^ l) ^ 2 := this
        _ = 4 * L ^ 2 * sin r ^ (2 * l) := by ring
    have hprod : (sin r / cos r) ^ (d - 1) * χ2 r ^ 2 ≤ 2 ^ (d - 1) * (4 * L ^ 2) * r ^ (2 * l + 1) := by
      calc (sin r / cos r) ^ (d - 1) * χ2 r ^ 2 ≤ (2 ^ (d - 1) * sin r) * (4 * L ^ 2 * sin r ^ (2 * l)) :=
            mul_le_mul ht hχ (by positivity) (by positivity)
        _ = 2 ^ (d - 1) * (4 * L ^ 2) * sin r ^ (2 * l + 1) := by ring
        _ ≤ 2 ^ (d - 1) * (4 * L ^ 2) * r ^ (2 * l + 1) := by
            gcongr
    have htpos : 0 < (sin r / cos r) ^ (d - 1) := by positivity
    have hW' : deriv χ1 r * χ2 r - χ1 r * deriv χ2 r = -K / (sin r / cos r) ^ (d - 1) := by
      have := hW r (hIoo r hr)
      field_simp
      linear_combination -this
    rw [hW', div_div, neg_div, neg_div, neg_le_neg_iff, hκ, div_div]
    exact div_le_div_of_nonneg_left hK.le (by positivity) hprod
  obtain ⟨φ, hφ, hφlim⟩ := pow_inv_bound κ hκpos l
  -- `G = Q - φ` is antitone
  have hG : AntitoneOn (fun r => χ1 r / χ2 r - φ r) (Ioo 0 r1) := by
    have hd' : ∀ r ∈ Ioo 0 r1, HasDerivAt (fun r => χ1 r / χ2 r - φ r)
        ((deriv χ1 r * χ2 r - χ1 r * deriv χ2 r) / χ2 r ^ 2 - -κ / r ^ (2 * l + 1)) r :=
      fun r hr => (hQ r hr).sub (hφ r hr.1)
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 r1) ?_ ?_ ?_
    · exact fun r hr => (hd' r hr).continuousAt.continuousWithinAt
    · rw [interior_Ioo]; exact fun r hr => (hd' r hr).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]; intro r hr; rw [(hd' r hr).deriv]; linarith [hQ' r hr]
  have hr2 : r1 / 2 ∈ Ioo 0 r1 := ⟨by positivity, by linarith⟩
  set C0 := χ1 (r1 / 2) / χ2 (r1 / 2) - φ (r1 / 2)
  have hlow2 : Tendsto (fun r => L / 2 * (-|C0| + φ r * sin r ^ l)) (𝓝[>] 0) atTop :=
    (tendsto_atTop_add_const_left _ _ hφlim).const_mul_atTop (by positivity)
  have hev := (hlow2.eventually_gt_atTop (max B 0)).and (Ioo_mem_nhdsGT hr2.1)
  obtain ⟨r, hr, hrr⟩ := hev.exists
  have hr' : r ∈ Ioo 0 r1 := ⟨hrr.1, hrr.2.trans hr2.2⟩
  obtain ⟨hs, hc⟩ := mem_aux (hIoo r hr')
  have hsl : 0 < sin r ^ l := pow_pos hs l
  have hsl1 : sin r ^ l ≤ 1 := pow_le_one₀ hs.le (sin_le_one r)
  have hmax := le_max_left B 0
  have hmax0 := le_max_right B 0
  have hGr := hG hr' hr2 hrr.2.le
  simp only at hGr
  -- `φ r * sin^l > |C0|`, so `φ r > |C0|`
  have hφs : |C0| < φ r * sin r ^ l := by
    have : 0 < L / 2 * (-|C0| + φ r * sin r ^ l) := lt_of_le_of_lt hmax0 hr
    have := (mul_pos_iff_of_pos_left (by positivity : (0:ℝ) < L / 2)).1 this
    linarith
  have hφpos : 0 < φ r := by
    by_contra hneg; push_neg at hneg
    have : φ r * sin r ^ l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hsl.le
    linarith [abs_nonneg C0]
  have hφge : φ r * sin r ^ l ≤ φ r := mul_le_of_le_one_right hφpos.le hsl1
  have hQr : C0 + φ r ≤ χ1 r / χ2 r := by linarith
  have hpos2 := hχpos r hr'
  have hCφ : 0 < C0 + φ r := by linarith [neg_abs_le C0]
  have key : (C0 + φ r) * (L / 2 * sin r ^ l) ≤ χ1 r := by
    calc (C0 + φ r) * (L / 2 * sin r ^ l) ≤ (χ1 r / χ2 r) * χ2 r :=
          mul_le_mul hQr (hlow r hr') (by positivity) (by linarith)
      _ = χ1 r := by field_simp
  have key2 : L / 2 * (-|C0| + φ r * sin r ^ l) ≤ (C0 + φ r) * (L / 2 * sin r ^ l) := by
    have : -|C0| ≤ C0 * sin r ^ l := by
      rcases le_or_gt 0 C0 with h0 | h0
      · nlinarith [abs_nonneg C0]
      · rw [abs_of_neg h0]; nlinarith
    nlinarith
  linarith [hB' r hr']

lemma unique_pos {χ1 χ2 : ℝ → ℝ} (h1 : IsRadialSolution d m R ω l χ1)
    (h2 : IsRadialSolution d m R ω l χ2) (hd : 2 ≤ d) (hreg : IsRegularAtOrigin χ1) {L : ℝ}
    (hL : 0 < L) (hlim : Tendsto (fun r => χ2 r / sin r ^ l) (𝓝[>] 0) (𝓝 L)) :
    ∃ c, ∀ r ∈ Ioo 0 (π / 2), χ1 r = c * χ2 r := by
  have hev := hlim.eventually (Ioo_mem_nhds (show L / 2 < L by linarith) (show L < 2 * L by linarith))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  set r1 := min u (π / 4)
  have hr1 : 0 < r1 := lt_min hu (by positivity)
  have hr1' : r1 ≤ π / 4 := min_le_right _ _
  have hIoo : ∀ r ∈ Ioo 0 r1, r ∈ Ioo 0 (π / 2) := fun r hr => ⟨hr.1, by linarith [hr.2, pi_pos]⟩
  have hb : ∀ r ∈ Ioo 0 r1, L / 2 * sin r ^ l ≤ χ2 r ∧ χ2 r ≤ 2 * L * sin r ^ l := by
    intro r hr
    have hs : 0 < sin r ^ l := pow_pos (mem_aux (hIoo r hr)).1 l
    have := hsub ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
    have this : L / 2 < χ2 r / sin r ^ l ∧ χ2 r / sin r ^ l < 2 * L := this
    rw [lt_div_iff₀ hs, div_lt_iff₀ hs] at this
    constructor <;> linarith [this.1, this.2]
  obtain ⟨K, hK⟩ := wronskian h1 h2 hd
  rcases lt_trichotomy K 0 with hK0 | hK0 | hK0
  · -- negate `χ1`
    exfalso
    have h1' := sol_lin h2 h1 0 (-1)
    refine blowup h1' h2 hd ?_ hr1 hr1' hL (fun r hr => (hb r hr).1) (fun r hr => (hb r hr).2)
      (neg_pos.2 hK0) (fun r hr => ?_)
    · obtain ⟨B, hB⟩ := hreg
      refine ⟨B, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      simpa using hB ⟨r, hr, rfl⟩
    · have hd1 : deriv (fun r => 0 * χ2 r + -1 * χ1 r) r = -deriv χ1 r := by
        have := ((sol_diff h1 hr).1.const_mul (-1 : ℝ)).const_add (0 * χ2 r)
        have e : (fun r => 0 * χ2 r + -1 * χ1 r) = fun x => 0 * χ2 r + -1 * χ1 x := by
          funext x; simp
        rw [e, this.deriv]; ring
      rw [hd1, ← hK r hr]; ring
  · -- Wronskian zero: proportional near 0, then everywhere
    have hW0 : ∀ r ∈ Ioo 0 r1, deriv χ1 r * χ2 r - χ1 r * deriv χ2 r = 0 := by
      intro r hr
      obtain ⟨hs, hc⟩ := mem_aux (hIoo r hr)
      have := hK r (hIoo r hr)
      rw [hK0] at this
      have ht : (sin r / cos r) ^ (d - 1) ≠ 0 := by positivity
      have := (mul_eq_zero.1 this).resolve_right ht
      linarith
    have hχpos : ∀ r ∈ Ioo 0 r1, 0 < χ2 r := fun r hr =>
      lt_of_lt_of_le (by have := (mem_aux (hIoo r hr)).1; positivity) (hb r hr).1
    have hQ : ∀ r ∈ Ioo 0 r1, HasDerivAt (fun r => χ1 r / χ2 r) 0 r := by
      intro r hr
      have := (sol_diff h1 (hIoo r hr)).1.div (sol_diff h2 (hIoo r hr)).1 (hχpos r hr).ne'
      rw [hW0 r hr, zero_div] at this
      exact this
    obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun r hr => (hQ r hr).differentiableAt.differentiableWithinAt) (fun r hr => (hQ r hr).deriv)
    refine ⟨c, fun r hr => ?_⟩
    have hψ := sol_lin h1 h2 1 (-c)
    have hz : ∀ r ∈ Ioo 0 r1, 1 * χ1 r + -c * χ2 r = 0 := by
      intro r hr
      have := hc r hr
      have hne := (hχpos r hr).ne'
      field_simp at this
      linarith
    have := vanish hψ (by omega) hr1 (by linarith [pi_pos]) hz r hr
    linarith
  · exact absurd (blowup h1 h2 hd hreg hr1 hr1' hL (fun r hr => (hb r hr).1)
      (fun r hr => (hb r hr).2) hK0 hK) id

lemma unique {χ1 χ2 : ℝ → ℝ} (h1 : IsRadialSolution d m R ω l χ1)
    (h2 : IsRadialSolution d m R ω l χ2) (hd : 2 ≤ d) (hreg : IsRegularAtOrigin χ1) {L : ℝ}
    (hL : L ≠ 0) (hlim : Tendsto (fun r => χ2 r / sin r ^ l) (𝓝[>] 0) (𝓝 L)) :
    ∃ c, ∀ r ∈ Ioo 0 (π / 2), χ1 r = c * χ2 r := by
  rcases lt_or_gt_of_ne hL with hL0 | hL0
  · have h2' := sol_lin h2 h2 0 (-1)
    have hlim' : Tendsto (fun r => (0 * χ2 r + -1 * χ2 r) / sin r ^ l) (𝓝[>] 0) (𝓝 (-L)) := by
      refine hlim.neg.congr fun r => ?_
      ring
    obtain ⟨c, hc⟩ := unique_pos h1 h2' hd hreg (neg_pos.2 hL0) hlim'
    exact ⟨-c, fun r hr => by rw [hc r hr]; ring⟩
  · exact unique_pos h1 h2 hd hreg hL0 hlim

end NN104U

end

section

open Real Finset Filter Topology MeasureTheory
open Giddings1999

namespace GDJac

noncomputable def mm (s t : ℕ) (x : ℝ) : ℝ := ((x-1)/2)^s * ((x+1)/2)^t

lemma hasDerivAt_mm (s t : ℕ) (x : ℝ) :
    HasDerivAt (mm s t) ((s * mm (s-1) t x + t * mm s (t-1) x)/2) x := by
  have h1 : HasDerivAt (fun x:ℝ => ((x-1)/2)^s) (s * ((x-1)/2)^(s-1) * (1/2)) x := by
    have := (((hasDerivAt_id x).sub_const 1).div_const 2).fun_pow s
    simpa using this
  have h2 : HasDerivAt (fun x:ℝ => ((x+1)/2)^t) (t * ((x+1)/2)^(t-1) * (1/2)) x := by
    have := (((hasDerivAt_id x).add_const 1).div_const 2).fun_pow t
    simpa using this
  have := h1.fun_mul h2
  unfold mm
  refine this.congr_deriv ?_
  ring

lemma hu (k t : ℕ) (x : ℝ) : (x-1)/2 * ((k:ℝ) * mm (k-1) t x) = k * mm k t x := by
  cases k with
  | zero => simp
  | succ j => simp only [mm, Nat.add_sub_cancel]; ring

lemma hv (s k : ℕ) (x : ℝ) : (x+1)/2 * ((k:ℝ) * mm s (k-1) x) = k * mm s k x := by
  cases k with
  | zero => simp
  | succ j => simp only [mm, Nat.add_sub_cancel]; ring

/-- second derivative of a monomial (as an explicit expression) -/
noncomputable def D2 (s t : ℕ) (x : ℝ) : ℝ :=
  (s * ((↑(s-1) * mm (s-1-1) t x + t * mm (s-1) (t-1) x)/2)
    + t * ((s * mm (s-1) (t-1) x + ↑(t-1) * mm s (t-1-1) x)/2))/2

noncomputable def D1 (s t : ℕ) (x : ℝ) : ℝ := (s * mm (s-1) t x + t * mm s (t-1) x)/2

lemma hasDerivAt_D1 (s t : ℕ) (x : ℝ) : HasDerivAt (D1 s t) (D2 s t x) x := by
  have := (((hasDerivAt_mm (s-1) t x).const_mul (s:ℝ)).fun_add
    ((hasDerivAt_mm s (t-1) x).const_mul (t:ℝ))).div_const 2
  unfold D1 D2
  convert this using 1

lemma mono (α β : ℝ) (s t : ℕ) (x : ℝ) :
    (1 - x^2) * D2 s t x + (β - α - (α+β+2)*x) * D1 s t x
      + ((s+t:ℕ):ℝ) * ((s+t:ℕ) + α + β + 1) * mm s t x
    = - (s * (s + α)) * mm (s-1) (t+1) x - (t * (t + β)) * mm (s+1) (t-1) x
      + (((s+t:ℕ):ℝ) * ((s+t:ℕ) + α + β + 1) - 2*s*t - (α+1)*t - (β+1)*s) * mm s t x := by
  unfold D1 D2
  rcases s with _ | _ | k <;> rcases t with _ | _ | j <;>
    simp only [mm, Nat.add_sub_cancel, Nat.zero_sub, Nat.sub_self] <;> push_cast <;> ring

lemma gbinom_succ (a : ℝ) (k : ℕ) : gbinom a (k+1) * (k+1) = gbinom a k * (a - k) := by
  unfold gbinom
  rw [descPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  field_simp

noncomputable def A (n : ℕ) (α β : ℝ) (s : ℕ) : ℝ := gbinom (n+α) (n-s) * gbinom (n+β) s

lemma A_rec (n : ℕ) (α β : ℝ) (j : ℕ) (hj : j < n) :
    ((j:ℝ)+1) * ((j:ℝ)+1+α) * A n α β (j+1) = ((n:ℝ)-j) * ((n:ℝ)-j+β) * A n α β j := by
  unfold A
  have h1 := gbinom_succ (n+β) j
  have h2 := gbinom_succ (n+α) (n-j-1)
  have e : n - j - 1 + 1 = n - j := by omega
  have e' : n - (j+1) = n - j - 1 := by omega
  rw [e] at h2
  rw [e']
  have c : ((n-j-1 : ℕ):ℝ) = n - j - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hj.le]; simp
  rw [c] at h2
  linear_combination ((↑j + 1 + α) * gbinom (↑n + α) (n - j - 1)) * h1
    - (gbinom (↑n + β) j * (↑n + β - ↑j)) * h2

noncomputable def P (n : ℕ) (α β x : ℝ) : ℝ := ∑ s ∈ range (n+1), A n α β s * mm s (n-s) x
noncomputable def P1 (n : ℕ) (α β x : ℝ) : ℝ := ∑ s ∈ range (n+1), A n α β s * D1 s (n-s) x
noncomputable def P2 (n : ℕ) (α β x : ℝ) : ℝ := ∑ s ∈ range (n+1), A n α β s * D2 s (n-s) x

lemma P_eq (n : ℕ) (α β x : ℝ) : P n α β x = jacobiP n α β x := by
  unfold P jacobiP A mm
  refine sum_congr rfl fun s _ => by ring

lemma hasDerivAt_P (n : ℕ) (α β x : ℝ) : HasDerivAt (P n α β) (P1 n α β x) x := by
  unfold P P1
  have := HasDerivAt.fun_sum (u := range (n+1)) (A := fun s y => A n α β s * mm s (n-s) y)
    (A' := fun s => A n α β s * D1 s (n-s) x) (x := x)
    (fun s _ => (hasDerivAt_mm s (n-s) x).const_mul _)
  exact this

lemma hasDerivAt_P1 (n : ℕ) (α β x : ℝ) : HasDerivAt (P1 n α β) (P2 n α β x) x := by
  unfold P1 P2
  exact HasDerivAt.fun_sum (u := range (n+1)) (A := fun s y => A n α β s * D1 s (n-s) y)
    (A' := fun s => A n α β s * D2 s (n-s) x) (x := x)
    (fun s _ => (hasDerivAt_D1 s (n-s) x).const_mul _)

lemma jacobi_ode (n : ℕ) (α β x : ℝ) :
    (1 - x^2) * P2 n α β x + (β - α - (α+β+2)*x) * P1 n α β x
      + (n:ℝ) * (n + α + β + 1) * P n α β x = 0 := by
  unfold P P1 P2
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  have hm : ∀ s ∈ range (n+1), (1 - x^2) * (A n α β s * D2 s (n-s) x)
      + (β - α - (α+β+2)*x) * (A n α β s * D1 s (n-s) x)
      + (n:ℝ) * (n + α + β + 1) * (A n α β s * mm s (n-s) x)
      = A n α β s * (- (s * (s + α)) * mm (s-1) (n-s+1) x
          - (((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * mm (s+1) (n-s-1) x)
        + A n α β s * (((n:ℝ) * (n + α + β + 1) - 2*s*(n-s:ℕ) - (α+1)*(n-s:ℕ) - (β+1)*s)
          * mm s (n-s) x) := by
    intro s hs
    have hsn : s + (n - s) = n := by have := mem_range.1 hs; omega
    have := mono α β s (n-s) x
    rw [hsn] at this
    linear_combination (A n α β s) * this
  rw [sum_congr rfl hm, sum_add_distrib]
  -- first part: reindex
  have S1 : ∑ s ∈ range (n+1), A n α β s * (- (s * (s + α)) * mm (s-1) (n-s+1) x)
      = - ∑ s ∈ range (n+1), (((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * A n α β s * mm s (n-s) x := by
    rw [sum_range_succ', sum_range_succ]
    simp only [Nat.cast_zero, zero_mul, neg_zero, mul_zero, add_zero, Nat.sub_self, zero_add]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have e : n - (j+1) + 1 = n - j := by omega
    rw [Nat.add_sub_cancel, e]
    have := A_rec n α β j hj'
    have c : ((n - j : ℕ):ℝ) = n - j := by rw [Nat.cast_sub hj'.le]
    rw [c]; push_cast
    linear_combination (-mm j (n-j) x) * this
  have S3 : ∑ s ∈ range (n+1), A n α β s * (-(((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * mm (s+1) (n-s-1) x)
      = - ∑ s ∈ range (n+1), ((s:ℝ) * (s + α)) * A n α β s * mm s (n-s) x := by
    rw [sum_range_succ, sum_range_succ']
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, neg_zero, mul_zero, add_zero, zero_add]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have e : n - j - 1 = n - (j+1) := by omega
    rw [e]
    have := A_rec n α β j hj'
    have c : ((n - j : ℕ):ℝ) = n - j := by rw [Nat.cast_sub hj'.le]
    rw [c]; push_cast
    linear_combination (mm (j+1) (n-(j+1)) x) * this
  have split : ∀ s ∈ range (n+1), A n α β s * (- (s * (s + α)) * mm (s-1) (n-s+1) x
          - (((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * mm (s+1) (n-s-1) x)
      = A n α β s * (- (s * (s + α)) * mm (s-1) (n-s+1) x)
        + A n α β s * (-(((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * mm (s+1) (n-s-1) x) := by
    intro s _; ring
  rw [sum_congr rfl split, sum_add_distrib, S1, S3, ← sum_neg_distrib, ← sum_neg_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun s hs => ?_
  have hs' := mem_range.1 hs
  have c : ((n - s : ℕ):ℝ) = n - s := by rw [Nat.cast_sub (by omega)]
  rw [c]; ring

end GDJac


namespace GDRad
open GDJac

lemma pow_pred_mul (l : ℕ) (s : ℝ) : (l:ℝ) * s^(l-1) * s = l * s^l := by
  cases l with
  | zero => simp
  | succ k => simp [pow_succ]; ring

/-- first derivative of the mode -/
lemma hasDerivAt_chi (n l : ℕ) (b α β r : ℝ) (hs : 0 < sin r) (hc : 0 < cos r) :
    HasDerivAt (fun r => sin r ^ l * cos r ^ b * P n α β (cos (2 * r)))
      (sin r ^ l * cos r ^ b * ((l * cos r / sin r - b * sin r / cos r) * P n α β (cos (2*r))
        + (-4 * sin r * cos r) * P1 n α β (cos (2*r)))) r := by
  have h1 : HasDerivAt (fun r => sin r ^ l) (l * sin r ^ (l-1) * cos r) r :=
    (hasDerivAt_sin r).fun_pow l
  have h2 : HasDerivAt (fun r => cos r ^ b) (b * cos r ^ (b - 1) * (-sin r)) r := by
    have := (hasDerivAt_cos r).rpow_const (p := b) (Or.inl hc.ne')
    refine this.congr_deriv ?_; ring
  have h3 : HasDerivAt (fun r => P n α β (cos (2 * r)))
      (P1 n α β (cos (2*r)) * (-sin (2*r) * 2)) r := by
    have hc2 : HasDerivAt (fun r => cos (2 * r)) (-sin (2*r) * 2) r := by
      have := ((hasDerivAt_id r).const_mul 2).cos
      simpa using this
    exact (hasDerivAt_P n α β _).comp r hc2
  have := (h1.fun_mul h2).fun_mul h3
  refine this.congr_deriv ?_
  rw [rpow_sub_one hc.ne', sin_two_mul]
  have e := pow_pred_mul l (sin r)
  field_simp
  linear_combination (cos r ^ 2 * P n α β (cos (2 * r))) * e

lemma hasDerivAt_D (n l : ℕ) (b α β r : ℝ) (hs : 0 < sin r) (hc : 0 < cos r) :
    HasDerivAt (fun r => sin r ^ l * cos r ^ b * ((l * cos r / sin r - b * sin r / cos r) * P n α β (cos (2*r))
        + (-4 * sin r * cos r) * P1 n α β (cos (2*r))))
      (sin r ^ l * cos r ^ b * (((l * cos r / sin r - b * sin r / cos r)^2 + (-l / sin r^2 - b / cos r^2))
          * P n α β (cos (2*r))
        + (2 * (l * cos r / sin r - b * sin r / cos r) * (-4 * sin r * cos r) + (-4 * (cos r^2 - sin r^2)))
          * P1 n α β (cos (2*r))
        + (-4 * sin r * cos r)^2 * P2 n α β (cos (2*r)))) r := by
  have h1 : HasDerivAt (fun r => sin r ^ l) (l * sin r ^ (l-1) * cos r) r :=
    (hasDerivAt_sin r).fun_pow l
  have h2 : HasDerivAt (fun r => cos r ^ b) (b * cos r ^ (b - 1) * (-sin r)) r := by
    have := (hasDerivAt_cos r).rpow_const (p := b) (Or.inl hc.ne')
    refine this.congr_deriv ?_; ring
  have hX : HasDerivAt (fun r => cos (2 * r)) (-4 * sin r * cos r) r := by
    have := ((hasDerivAt_id r).const_mul 2).cos
    refine (by simpa using this : HasDerivAt (fun r => cos (2 * r)) (-sin (2*r) * 2) r).congr_deriv ?_
    rw [sin_two_mul]; ring
  have hPX := (hasDerivAt_P n α β _).comp r hX
  have hP1X := (hasDerivAt_P1 n α β _).comp r hX
  have hg : HasDerivAt (fun r => l * cos r / sin r - b * sin r / cos r) (-l / sin r^2 - b / cos r^2) r := by
    have := (((hasDerivAt_cos r).const_mul (l:ℝ)).div (hasDerivAt_sin r) hs.ne').fun_sub
      (((hasDerivAt_sin r).const_mul b).div (hasDerivAt_cos r) hc.ne')
    refine this.congr_deriv ?_
    have py := sin_sq_add_cos_sq r
    field_simp
    linear_combination (-(l:ℝ) * cos r ^ 2 - b * sin r ^ 2) * py
  have hh : HasDerivAt (fun r => -4 * sin r * cos r) (-4 * (cos r^2 - sin r^2)) r := by
    have := ((hasDerivAt_sin r).const_mul (-4:ℝ)).fun_mul (hasDerivAt_cos r)
    refine this.congr_deriv ?_; ring
  have h0 : HasDerivAt (fun r => sin r ^ l * cos r ^ b)
      (sin r ^ l * cos r ^ b * (l * cos r / sin r - b * sin r / cos r)) r := by
    have := h1.fun_mul h2
    refine this.congr_deriv ?_
    rw [rpow_sub_one hc.ne']
    have e := pow_pred_mul l (sin r)
    field_simp
    linear_combination (cos r ^ 2) * e
  have := h0.fun_mul ((hg.fun_mul hPX).fun_add (hh.fun_mul hP1X))
  refine this.congr_deriv ?_
  simp only [Function.comp]
  ring

lemma P_contDiff (n : ℕ) (α β : ℝ) : ContDiff ℝ 2 (P n α β) := by
  unfold P mm; fun_prop

lemma radial (d : ℕ) (m R : ℝ) (n l : ℕ) :
    IsRadialSolution d m R (omegaNL d m R n l) l (modeRadial d m R n l) := by
  set b := twoHPlus d m R with hb
  set ν := nu d m R with hν
  set α : ℝ := (l:ℝ) + (d:ℝ)/2 - 1 with hα
  have hmode : modeRadial d m R n l = fun r => sin r ^ l * cos r ^ b * P n α ν (cos (2*r)) := by
    funext r; simp only [modeRadial, P_eq]; rfl
  have hbν : b = d/2 + ν := rfl
  have hM : m^2 * R^2 = b * (b - d) := by
    have hs : Real.sqrt ((d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2) ^ 2 = (d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2 :=
      Real.sq_sqrt (by positivity)
    simp only [hb, twoHPlus, nu]; nlinarith [hs]
  have hω : omegaNL d m R n l = b + 2*n + l := rfl
  refine ⟨?_, ?_⟩
  · rw [hmode]
    intro r hr
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    apply ContDiffAt.contDiffWithinAt
    refine ((contDiff_sin.pow l).contDiffAt.mul ?_).mul ?_
    · exact (contDiffAt_rpow_const_of_ne hc.ne').comp r contDiff_cos.contDiffAt
    · exact ((P_contDiff n α ν).comp (contDiff_cos.comp (contDiff_const.mul contDiff_id))).contDiffAt
  · intro r hr
    rw [hmode]
    have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2, pi_pos])
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    have hev : deriv (fun r => sin r ^ l * cos r ^ b * P n α ν (cos (2 * r))) =ᶠ[𝓝 r]
        (fun r => sin r ^ l * cos r ^ b * ((l * cos r / sin r - b * sin r / cos r) * P n α ν (cos (2*r))
          + (-4 * sin r * cos r) * P1 n α ν (cos (2*r)))) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
      have hs' : 0 < sin r' := sin_pos_of_pos_of_lt_pi hr'.1 (by linarith [hr'.2, pi_pos])
      have hc' : 0 < cos r' := cos_pos_of_mem_Ioo ⟨by linarith [hr'.1, pi_pos], hr'.2⟩
      exact (hasDerivAt_chi n l b α ν r' hs' hc').deriv
    rw [hev.deriv_eq, (hasDerivAt_chi n l b α ν r hs hc).deriv, (hasDerivAt_D n l b α ν r hs hc).deriv]
    have jac := jacobi_ode n α ν (cos (2*r))
    rw [cos_two_mul] at jac
    beta_reduce
    rw [cos_two_mul, hω, hM]
    have py := sin_sq_add_cos_sq r
    set S := sin r
    set C := cos r
    set χ0 := S ^ l * C ^ b
    set Q0 := P n α ν (2 * C ^ 2 - 1)
    set Q1 := P1 n α ν (2 * C ^ 2 - 1)
    set Q2 := P2 n α ν (2 * C ^ 2 - 1)
    have ecP : (l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2) + ((d:ℝ) - 1) / (S * C) * (l * C / S - b * S / C)
        + (b + 2*n + l)^2 - l * (l + d - 2) / S^2 - b * (b - d) / C^2 = 4 * n * (n + α + ν + 1) := by
      rw [hα, hbν]
      field_simp
      linear_combination (4 * (l:ℝ)^2 * C^2 + ((d:ℝ) + 2*ν)^2 * S^2) * py
    have ecP1 : 2 * (l * C / S - b * S / C) * (-4 * S * C) + (-4 * (C^2 - S^2))
        + ((d:ℝ) - 1) / (S * C) * (-4 * S * C) = 4 * (ν - α - (α + ν + 2) * (2 * C ^ 2 - 1)) := by
      rw [hα, hbν]
      field_simp
      linear_combination (2 + 2 * (d:ℝ) + 4 * ν) * py
    have eh : (-4 * S * C)^2 = 4 * (1 - (2 * C ^ 2 - 1) ^ 2) := by
      linear_combination (16 * C^2) * py
    have key : χ0 * (((l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2)) * Q0
          + (2 * (l * C / S - b * S / C) * (-4 * S * C) + (-4 * (C^2 - S^2))) * Q1
          + (-4 * S * C)^2 * Q2)
        + ((d:ℝ) - 1) / (S * C) * (χ0 * ((l * C / S - b * S / C) * Q0 + (-4 * S * C) * Q1))
        + (b + 2*n + l)^2 * (χ0 * Q0) - l * (l + d - 2) / S^2 * (χ0 * Q0) - b * (b - d) / C^2 * (χ0 * Q0)
        = χ0 * (((l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2) + ((d:ℝ) - 1) / (S * C) * (l * C / S - b * S / C)
        + (b + 2*n + l)^2 - l * (l + d - 2) / S^2 - b * (b - d) / C^2) * Q0
          + (2 * (l * C / S - b * S / C) * (-4 * S * C) + (-4 * (C^2 - S^2))
        + ((d:ℝ) - 1) / (S * C) * (-4 * S * C)) * Q1 + (-4 * S * C)^2 * Q2) := by ring
    rw [key, ecP, ecP1, eh]
    linear_combination (4 * χ0) * jac

end GDRad



namespace GDNorm

lemma asym (d : ℕ) (m R : ℝ) (n l : ℕ) :
    ∃ k : ℝ, k ≠ 0 ∧
      Tendsto (fun r => modeRadial d m R n l r / cos r ^ twoHPlus d m R) (𝓝[<] (π / 2)) (𝓝 k) := by
  set α : ℝ := (l : ℝ) + (d : ℝ) / 2 - 1
  set ν := nu d m R
  have hν : 0 ≤ ν := by simp only [ν, nu]; positivity
  have hP : jacobiP n α ν (-1) = gbinom (n + ν) n * (-1) ^ n := by
    unfold jacobiP
    rw [Finset.sum_eq_single n]
    · simp [gbinom]; left; norm_num
    · intro s hs hsn
      have : n - s ≠ 0 := by
        have := Finset.mem_range.1 hs; omega
      simp [zero_pow this]
    · intro h; exact absurd (Finset.self_mem_range_succ n) h
  have hg : 0 < gbinom (n + ν) n := by
    unfold gbinom
    apply div_pos _ (by positivity)
    apply descPochhammer_pos
    linarith
  refine ⟨jacobiP n α ν (-1), ?_, ?_⟩
  · rw [hP]; exact mul_ne_zero hg.ne' (pow_ne_zero _ (by norm_num))
  have hcont : Continuous (fun r : ℝ => sin r ^ l * jacobiP n α ν (cos (2 * r))) := by
    unfold jacobiP; fun_prop
  have hlim := (hcont.tendsto (π / 2)).mono_left (nhdsWithin_le_nhds (s := Set.Iio (π/2)))
  have h2 : 2 * (π / 2) = π := by ring
  simp only [sin_pi_div_two, h2, cos_pi, one_pow, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < π / 2 by positivity)] with r hr
  have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
  have hb : 0 < cos r ^ twoHPlus d m R := rpow_pos_of_pos hc _
  simp only [modeRadial, α, ν]
  field_simp

lemma normalizable (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (n l : ℕ) :
    IsNormalizableMode d m R (omegaNL d m R n l) l (modeRadial d m R n l) := by
  set b := twoHPlus d m R with hb
  set ν := nu d m R with hνdef
  have hν : 0 ≤ ν := by simp only [ν, nu]; positivity
  set α : ℝ := (l:ℝ) + (d:ℝ)/2 - 1
  have hPc : Continuous (fun r : ℝ => jacobiP n α ν (cos (2 * r))) := by
    unfold jacobiP; fun_prop
  refine ⟨GDRad.radial d m R n l, ?_, ?_, ?_⟩
  · obtain ⟨k, hk, hlim⟩ := asym d m R n l
    have hev : ∀ᶠ r in 𝓝[<] (π / 2), modeRadial d m R n l r / cos r ^ b ≠ 0 :=
      hlim.eventually (isOpen_ne.mem_nhds hk)
    have hev2 := hev.and (Ioo_mem_nhdsLT (show (0:ℝ) < π / 2 by positivity))
    obtain ⟨r, hr1, hr2⟩ := hev2.exists
    refine ⟨r, hr2, fun h => hr1 ?_⟩
    simp [h]
  · -- bounded near the origin
    have hcont : ContinuousOn (fun r => |modeRadial d m R n l r|) (Set.Icc 0 (π / 4)) := by
      apply ContinuousOn.abs
      unfold modeRadial
      intro r hr
      have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], by linarith [hr.2, pi_pos]⟩
      apply ContinuousAt.continuousWithinAt
      refine ((continuous_sin.pow l).continuousAt.mul ?_).mul hPc.continuousAt
      exact (Real.continuousAt_rpow_const _ _ (Or.inl hc.ne')).comp continuous_cos.continuousAt
    exact ((isCompact_Icc.image_of_continuousOn hcont).bddAbove).mono
      (Set.image_mono Set.Ioc_subset_Icc_self)
  · -- finite KG norm
    unfold HasFiniteKGNorm
    set G : ℝ → ℝ := fun r => sin r ^ (d - 1 + 2 * l) * cos r ^ (2 * ν + 1) *
      jacobiP n α ν (cos (2 * r)) ^ 2
    have hG : Continuous G := by
      have : Continuous (fun r : ℝ => cos r ^ (2 * ν + 1)) :=
        (Real.continuous_rpow_const (by linarith)).comp continuous_cos
      exact ((continuous_sin.pow _).mul this).mul (hPc.pow 2)
    have hint : IntegrableOn G (Set.Ioo 0 (π / 2)) :=
      (hG.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    refine hint.congr_fun (fun r hr => ?_) measurableSet_Ioo
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    have e1 : (cos r ^ b) ^ 2 = (cos r) ^ (d - 1) * cos r ^ (2 * ν + 1) := by
      rw [← rpow_natCast (cos r ^ b), ← rpow_mul hc.le, ← rpow_natCast (cos r), ← rpow_add hc]
      congr 1
      rw [Nat.cast_sub (by omega)]; simp only [hb, twoHPlus, ν]; push_cast; ring
    simp only [G, modeRadial, tan_eq_sin_div_cos, div_pow]
    rw [mul_pow, mul_pow, e1, pow_add, pow_mul]
    field_simp
    have hαe : α = (2 * (l:ℝ) + d - 2) / 2 := by simp only [α]; ring
    rw [hαe, ← pow_mul, ← pow_mul, mul_comm 2 l]

end GDNorm

end

section

open Real Filter Topology Set MeasureTheory
open Giddings1999

namespace NN104G

lemma dp_pos (n : ℕ) (α : ℝ) (hα : 0 ≤ α) : ∀ k ≤ n, 0 < (descPochhammer ℝ k).eval ((n:ℝ) + α) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [descPochhammer_succ_eval]
    have : (k:ℝ) + 1 ≤ n := by exact_mod_cast hk
    exact mul_pos (ih (by omega)) (by linarith)

lemma jacobiP_one (n : ℕ) (α β : ℝ) (hα : 0 ≤ α) : jacobiP n α β 1 ≠ 0 := by
  unfold jacobiP
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.sub_zero, pow_zero, mul_one, sub_self, zero_div]
    unfold gbinom
    simp only [descPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, Nat.cast_one,
      div_one, mul_one]
    norm_num
    exact ⟨(dp_pos n α hα n le_rfl).ne', Nat.factorial_ne_zero n⟩
  · intro s _ hs
    simp [zero_pow hs]
  · intro h; simp at h

lemma mode_lim (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (n l : ℕ) :
    ∃ L : ℝ, L ≠ 0 ∧ Tendsto (fun r => modeRadial d m R n l r / sin r ^ l) (𝓝[>] 0) (𝓝 L) := by
  set α : ℝ := (l:ℝ) + (d:ℝ)/2 - 1
  have hα : 0 ≤ α := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    simp only [α]; linarith [l.cast_nonneg (α := ℝ)]
  refine ⟨jacobiP n α (nu d m R) 1, jacobiP_one n α _ hα, ?_⟩
  have hPc : Continuous (fun r : ℝ => jacobiP n α (nu d m R) (cos (2 * r))) := by
    unfold jacobiP; fun_prop
  have h1 : Tendsto (fun r => cos r ^ twoHPlus d m R * jacobiP n α (nu d m R) (cos (2 * r)))
      (𝓝 0) (𝓝 (1 * jacobiP n α (nu d m R) 1)) := by
    have hc : Tendsto (fun r => cos r ^ twoHPlus d m R) (𝓝 0) (𝓝 1) := by
      have := ((Real.continuousAt_rpow_const (cos 0) (twoHPlus d m R)
        (Or.inl (by rw [cos_zero]; norm_num))).comp (continuous_cos.continuousAt (x := 0)))
      have h := this.tendsto
      rw [Function.comp_apply, cos_zero, one_rpow] at h
      exact h
    have hp : Tendsto (fun r => jacobiP n α (nu d m R) (cos (2 * r))) (𝓝 0)
        (𝓝 (jacobiP n α (nu d m R) 1)) := by
      have := hPc.tendsto 0
      simpa using this
    exact hc.mul hp
  rw [one_mul] at h1
  refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < π / 2 by positivity)] with r hr
  have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2, pi_pos])
  have hne : sin r ^ l ≠ 0 := (pow_pos hs l).ne'
  simp only [modeRadial, α]
  field_simp

lemma mode_radial_abs (d : ℕ) (m R ω : ℝ) (n l : ℕ) (hω : |ω| = omegaNL d m R n l) :
    IsRadialSolution d m R ω l (modeRadial d m R n l) := by
  rcases le_or_gt 0 ω with h | h
  · rw [abs_of_nonneg h] at hω; rw [hω]; exact GDRad.radial d m R n l
  · rw [abs_of_neg h] at hω
    rw [show ω = -omegaNL d m R n l by linarith, NN104U.sol_neg_ω]
    exact GDRad.radial d m R n l

/-- a regular solution behaving like `cos^{2h₋}` at `π/2` has infinite KG norm -/
lemma not_KG (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (l : ℕ) (χ ψ : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (heq : ∀ r ∈ Ioo 0 (π / 2), χ r = c * ψ r)
    (hlim : Tendsto (fun r => ψ r / cos r ^ twoHMinus d m R) (𝓝[<] (π / 2)) (𝓝 1)) :
    ¬ HasFiniteKGNorm d χ := by
  intro hKG
  set b := twoHMinus d m R
  set ν := nu d m R
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hνge : (d:ℝ) / 2 ≤ ν := by
    have : (d:ℝ) ≤ Real.sqrt ((d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (m * R)])
    simp only [ν, nu]; linarith
  have hev := (hlim.eventually (Ioi_mem_nhds (show (1:ℝ)/2 < 1 by norm_num))).and
    (Ioo_mem_nhdsLT (show π / 4 < π / 2 by linarith [pi_pos]))
  obtain ⟨a0, ha0, hsub0⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  set a := max a0 (π / 4)
  have ha : a < π / 2 := max_lt ha0 (by linarith [pi_pos])
  have ha4 : π / 4 ≤ a := le_max_right _ _
  have hsub : ∀ {r}, r ∈ Ioo a (π / 2) → _ := fun {r} hr =>
    hsub0 ⟨lt_of_le_of_lt (le_max_left _ _) hr.1, hr.2⟩
  set κ0 := c ^ 2 / 4 * (1 / 2) ^ (d - 1)
  have hκ0 : 0 < κ0 := by positivity
  have hbound : ∀ r ∈ Ioo a (π / 2), κ0 * (π / 2 - r)⁻¹ ≤ tan r ^ (d - 1) * χ r ^ 2 := by
    intro r hr
    obtain ⟨h1, h2⟩ := hsub hr
    have h1 : 1 / 2 < ψ r / cos r ^ b := h1
    have hr0 : r ∈ Ioo 0 (π / 2) := ⟨by linarith [h2.1, pi_pos], h2.2⟩
    obtain ⟨hs, hcs⟩ := NN104U.mem_aux hr0
    have hcb : 0 < cos r ^ b := rpow_pos_of_pos hcs b
    have hψ : cos r ^ b / 2 < ψ r := by
      rw [lt_div_iff₀ hcb] at h1; linarith
    have hs2 : 1 / 2 ≤ sin r := by
      rw [← sin_pi_div_six]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) h2.2.le (by linarith [h2.1, pi_pos])
    have hcr : cos r ≤ π / 2 - r := by
      rw [← sin_pi_div_two_sub]; exact (sin_lt (by linarith [h2.2])).le
    have hc1 : cos r ≤ 1 := cos_le_one r
    -- tan^(d-1) * cos^(2b) ≥ (1/2)^(d-1) / cos
    have hpow : (cos r)⁻¹ ≤ (cos r ^ b) ^ 2 / cos r ^ (d - 1) := by
      rw [← rpow_natCast (cos r ^ b), ← rpow_mul hcs.le, ← rpow_natCast (cos r), ← rpow_sub hcs,
        ← rpow_neg_one]
      apply rpow_le_rpow_of_exponent_ge hcs hc1
      rw [Nat.cast_sub (by omega)]
      simp only [b, twoHMinus]; push_cast; linarith
    have htan : tan r ^ (d - 1) * χ r ^ 2 ≥ c ^ 2 / 4 * (sin r ^ (d - 1) * ((cos r ^ b) ^ 2 / cos r ^ (d - 1))) := by
      rw [heq r hr0, tan_eq_sin_div_cos, div_pow]
      have : (cos r ^ b / 2) ^ 2 ≤ ψ r ^ 2 := pow_le_pow_left₀ (by positivity) hψ.le 2
      have hcd : 0 < cos r ^ (d - 1) := by positivity
      calc c ^ 2 / 4 * (sin r ^ (d - 1) * ((cos r ^ b) ^ 2 / cos r ^ (d - 1)))
          = sin r ^ (d - 1) / cos r ^ (d - 1) * (c ^ 2 * (cos r ^ b / 2) ^ 2) := by ring
        _ ≤ sin r ^ (d - 1) / cos r ^ (d - 1) * (c ^ 2 * ψ r ^ 2) := by gcongr
        _ = sin r ^ (d - 1) / cos r ^ (d - 1) * (c * ψ r) ^ 2 := by ring
    have hsd : (1 / 2 : ℝ) ^ (d - 1) ≤ sin r ^ (d - 1) := pow_le_pow_left₀ (by norm_num) hs2 _
    have hinv : (π / 2 - r)⁻¹ ≤ (cos r)⁻¹ := inv_anti₀ hcs hcr
    calc κ0 * (π / 2 - r)⁻¹ ≤ c ^ 2 / 4 * ((1 / 2) ^ (d - 1) * (cos r)⁻¹) := by
          simp only [κ0]; rw [mul_assoc]; gcongr
      _ ≤ c ^ 2 / 4 * (sin r ^ (d - 1) * ((cos r ^ b) ^ 2 / cos r ^ (d - 1))) := by gcongr
      _ ≤ _ := htan
  have hint : IntegrableOn (fun r => (π / 2 - r)⁻¹) (Ioo a (π / 2)) := by
    have hK := (hKG.mono_set (Ioo_subset_Ioo_left (show 0 ≤ a by linarith [ha4, pi_pos]))).const_mul κ0⁻¹
    refine hK.mono' ?_ ?_
    · exact ((continuousOn_const.sub continuousOn_id).inv₀ fun r hr => by
        show π / 2 - r ≠ 0; exact (sub_pos.2 hr.2).ne').aestronglyMeasurable measurableSet_Ioo
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun r hr => ?_)
      have hpos : 0 < π / 2 - r := by linarith [hr.2]
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
      have := hbound r hr
      rw [le_inv_mul_iff₀ hκ0]
      exact this
  have hII : IntervalIntegrable (fun x => (x - π / 2)⁻¹) volume a (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le]
    refine hint.neg.congr_fun (fun r hr => ?_) measurableSet_Ioo
    simp only [Pi.neg_apply]
    rw [← inv_neg, neg_sub]
  rw [intervalIntegrable_sub_inv_iff] at hII
  rcases hII with h | h
  · linarith
  · exact h (by rw [uIcc_of_le ha.le]; exact ⟨ha.le, le_rfl⟩)

theorem goal (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R)
    (ω : ℝ) (l : ℕ) (χ : ℝ → ℝ) :
    IsNormalizableMode d m R ω l χ ↔
      ∃ n : ℕ, |ω| = omegaNL d m R n l ∧
        ∃ c : ℝ, c ≠ 0 ∧ Set.EqOn χ (fun r => c * modeRadial d m R n l r) (Set.Ioo 0 (π / 2)) := by
  constructor
  · rintro ⟨hrad, ⟨r0, hr0, hne⟩, hreg, hKG⟩
    by_cases hω : ∃ n : ℕ, |ω| = omegaNL d m R n l
    · obtain ⟨n, hn⟩ := hω
      obtain ⟨L, hL, hlim⟩ := mode_lim d hd m R n l
      obtain ⟨c, hc⟩ := NN104U.unique hrad (mode_radial_abs d m R ω n l hn) hd hreg hL hlim
      refine ⟨n, hn, c, ?_, fun r hr => hc r hr⟩
      rintro rfl
      exact hne (by rw [hc r0 hr0, zero_mul])
    · push_neg at hω
      exfalso
      obtain ⟨ψ, hψrad, -, hψlim, L, hL, hψ0⟩ := NN104.main d hd m R hR ω l hω
      obtain ⟨c, hc⟩ := NN104U.unique hrad hψrad hd hreg hL hψ0
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hne (by rw [hc r0 hr0, zero_mul])
      exact not_KG d hd m R l χ ψ c hc0 hc hψlim hKG
  · rintro ⟨n, hn, c, hc, heq⟩
    obtain ⟨-, ⟨r0, hr0, hne⟩, ⟨B, hB⟩, hKG⟩ := GDNorm.normalizable d hd m R n l
    have hmr := mode_radial_abs d m R ω n l hn
    refine ⟨?_, ⟨r0, hr0, ?_⟩, ?_, ?_⟩
    · refine NN104U.sol_congr (NN104U.sol_lin hmr hmr c 0) (fun r hr => ?_)
      simp only [heq hr, zero_mul, add_zero]
    · rw [heq hr0]; exact mul_ne_zero hc hne
    · refine ⟨|c| * B, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      have hr' : r ∈ Ioo 0 (π / 2) := ⟨hr.1, by linarith [hr.2, pi_pos]⟩
      simp only
      rw [heq hr', abs_mul]
      exact mul_le_mul_of_nonneg_left (hB ⟨r, hr, rfl⟩) (abs_nonneg c)
    · unfold HasFiniteKGNorm at hKG ⊢
      refine IntegrableOn.congr_fun (hKG.const_mul (c ^ 2)) (fun r hr => ?_) measurableSet_Ioo
      simp only [heq hr]; ring

end NN104G

end


open Real Filter Topology
open Giddings1999

theorem solution (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R)
    (ω : ℝ) (l : ℕ) (χ : ℝ → ℝ) :
    IsNormalizableMode d m R ω l χ ↔
      ∃ n : ℕ, |ω| = omegaNL d m R n l ∧
        ∃ c : ℝ, c ≠ 0 ∧ Set.EqOn χ (fun r => c * modeRadial d m R n l r) (Set.Ioo 0 (π / 2)) :=
  NN104G.goal d hd m R hR ω l χ
