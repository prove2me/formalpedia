-- Prove2me | solution 1 for Giddings1999.nonNormalizable_mode_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T04:35:26.096802+00:00
-- url     : https://prove2.me/submissions/71395eaa-3dbc-4fe7-87fd-cce613df36ff

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
      Tendsto (fun r => χ r / cos r ^ twoHMinus d m R) (𝓝[<] (π / 2)) (𝓝 1) := by
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
  refine ⟨fun r => sin r ^ l * cos r ^ b * P (cos (2 * r)), hrad, ?_, ?_⟩
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
    have hcont : ContinuousOn (ser c) (Icc 0 1) := by
      refine continuousOn_tsum (u := fun n => |c n|) (fun n => by fun_prop) hcsum fun n z hz => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hz.1]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hz.1 hz.2)
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

end NN104

end


open Real Filter Topology
open Giddings1999

theorem solution (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R) (ω : ℝ) (l : ℕ)
    (hω : ∀ n : ℕ, |ω| ≠ omegaNL d m R n l) :
    ∃ χ : ℝ → ℝ, IsRadialSolution d m R ω l χ ∧ IsRegularAtOrigin χ ∧
      Tendsto (fun r => χ r / cos r ^ twoHMinus d m R) (𝓝[<] (π / 2)) (𝓝 1) :=
  NN104.main d hd m R hR ω l hω
