-- Prove2me | solution 1 for IntMul.HvdH.Ref.mkParams_s_spec
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T21:19:35.323582+00:00
-- url     : https://prove2.me/submissions/d1b87ee2-adeb-4a58-a6f3-a40a2a3a4752

import Definitions.Def_IntMul_HvdH_MachineRef
import Theorems.Thm_IntMul_HvdH_coprime_window
import Definitions.Def_IntMul_HvdH_ConvR
import Mathlib

set_option maxHeartbeats 1000000

theorem IntMul.HvdH.Ref.ns_anchor : True := trivial

-- ===== Solutions.HvdH.SynId
section

open Complex

namespace IntMul.HvdH.SynId
open IntMul.HvdH

/-- Evaluation of a coefficient array at `z` (a root of `y^r + 1`). -/
noncomputable def ev (r : ℕ) (z : ℂ) (a : ℕ → ℂ) : ℂ := ∑ c ∈ Finset.range r, a c * z ^ c

/-! ### Evaluating arrays over `R` -/

/-- Evaluate the `R`-entry at position `k` at the root `z`. -/
noncomputable def E (r : ℕ) (z : ℂ) {d : ℕ} (u : (Fin (d + 1) → ℕ) → ℂ) (k : Fin d → ℕ) : ℂ :=
  ev r z (fun c => u (Fin.snoc k c))

/-! ### The convolution theorem on boxes -/

/-! ### The convolution identity over `R` -/

end IntMul.HvdH.SynId

end

-- ===== Solutions.HvdH.Coprime
section

namespace IntMul.HvdH.Cop

/-- One group of the parameter choice: below `(1-η) t` with `η = 1/(4d)` there are `d` numbers
`1 + Q (m₀ - i)` in `((1-2η) t, (1-η) t]`. -/
lemma group_choice (d t Q : ℕ) (hd : 1 ≤ d) (hQ : 0 < Q) (ht : 4 * d * d * Q + 4 * d ≤ t) :
    d ≤ ((4 * d - 1) * t - 4 * d) / (4 * d * Q) ∧ ∀ i < d,
      (4 * d - 2) * t < 4 * d * (1 + Q * (((4 * d - 1) * t - 4 * d) / (4 * d * Q) - i)) ∧
      4 * d * (1 + Q * (((4 * d - 1) * t - 4 * d) / (4 * d * Q) - i)) ≤ (4 * d - 1) * t := by
  set N := 4 * d * Q with hN
  have hN0 : 0 < N := by positivity
  set a := (4 * d - 1) * t - 4 * d with ha
  set m0 := a / N with hm0
  have h1 : N * m0 ≤ a := Nat.mul_div_le a N
  have h2 : a < N * (m0 + 1) := Nat.lt_mul_div_succ a hN0
  have h4d : 4 ≤ 4 * d := by omega
  have hta : (4 * d - 1) * t = a + 4 * d := by
    have : 4 * d ≤ (4 * d - 1) * t := by
      calc 4 * d ≤ t := by nlinarith
        _ ≤ (4 * d - 1) * t := Nat.le_mul_of_pos_left t (by omega)
    omega
  have hNd : N * d ≤ t := by
    have : N * d = 4 * d * d * Q := by rw [hN]; ring
    omega
  have hm0d : d ≤ m0 := by
    by_contra hc
    push Not at hc
    have : N * (m0 + 1) ≤ N * d := Nat.mul_le_mul_left N hc
    -- a < N d ≤ t but a = (4d-1) t - 4d ≥ 3t - 4d ≥ t
    have h3 : 3 * t ≤ (4 * d - 1) * t := Nat.mul_le_mul_right t (by omega)
    omega
  refine ⟨hm0d, fun i hi => ?_⟩
  have hsub : Q * (m0 - i) = Q * m0 - Q * i := Nat.mul_sub _ _ _
  have hNi : N * i ≤ N * m0 := Nat.mul_le_mul_left N (by omega)
  have hNi' : N * i + N ≤ N * d := by
    have := Nat.mul_le_mul_left N (show i + 1 ≤ d by omega); rwa [mul_add, mul_one] at this
  have hA : 4 * d * (Q * m0) = N * m0 := by rw [hN]; ring
  have hB : 4 * d * (Q * i) = N * i := by rw [hN]; ring
  have e1 : 4 * d * (1 + Q * (m0 - i)) = 4 * d + (N * m0 - N * i) := by
    rw [Nat.mul_sub, mul_add, mul_one, Nat.mul_sub, hA, hB]
  have h3 : (4 * d - 2) * t + t = (4 * d - 1) * t := by
    rw [← Nat.succ_mul]; congr 1; omega
  rw [e1]
  rw [mul_add, mul_one] at h2
  generalize N * m0 = P at *
  generalize N * i = Pi at *
  generalize N * d = Pd at *
  constructor
  · omega
  · omega

end IntMul.HvdH.Cop

end

-- ===== Solutions.HvdH.Ref.MkParams
section

/-! The parameters `mkParams K N` meet the conditions of `refStep_correct` for large `N`. -/

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

theorem copS_spec (d d' r : ℕ) (hd : 1 ≤ d) (hd' : d' ≤ d) (hr : 2 ∣ r)
    (hbig : 64 * d ^ 2 * (256 * d ^ 2).factorial ≤ r) :
    (∀ i < d, Odd ((copS d d' r).getD i 1)) ∧
    (∀ i < d, ∀ j < d, i ≠ j → Nat.Coprime ((copS d d' r).getD i 1) ((copS d d' r).getD j 1)) ∧
      ∀ i < d, (4 * d - 2) * (if i < d' then r / 2 else r) < 4 * d * (copS d d' r).getD i 1 ∧
        4 * d * (copS d d' r).getD i 1 ≤ (4 * d - 1) * (if i < d' then r / 2 else r) := by
  set D := 256 * d ^ 2 with hD
  set F := D.factorial with hF
  have hF0 : 0 < F := Nat.factorial_pos D
  set Q := 2 * F * (r / (2 * F * D) + 1) with hQ
  have hQ0 : 0 < Q := by positivity
  have hD0 : 0 < D := by positivity
  -- `Q D > r` and `Q ≤ r / D + 2F`
  have hQD : r < Q * D := by
    have := Nat.lt_div_mul_add (a := r) (show 0 < 2 * F * D by positivity)
    rw [hQ]; nlinarith
  have hQle : Q * D ≤ r + 2 * F * D := by
    rw [hQ, mul_add, mul_one, add_mul]
    have := Nat.div_mul_le_self r (2 * F * D)
    nlinarith
  -- both groups satisfy the size hypothesis
  have hbig' : 64 * d ^ 2 * F ≤ r := hbig
  have hsize : ∀ t, r ≤ 2 * t → 4 * d * d * Q + 4 * d ≤ t := by
    intro t ht
    -- 4 d² Q * 64 = Q * D / 4 * ... : 256 d² Q = Q D ≤ r + 2 F D
    have e : 256 * (4 * d * d * Q) = 4 * (Q * D) := by rw [hD]; ring
    have hFD : 2 * F * D = 512 * d ^ 2 * F := by rw [hD]; ring
    have h4d : 64 * 4 * d ≤ r := by
      have hDF : D ≤ F := Nat.self_le_factorial D
      have hd2 : d ≤ d ^ 2 := by nlinarith
      have : 64 * 4 * d ≤ 64 * d ^ 2 * D := by
        rw [hD]
        have : 1 ≤ d ^ 2 := by nlinarith
        nlinarith
      have : 64 * d ^ 2 * D ≤ 64 * d ^ 2 * F := Nat.mul_le_mul_left _ hDF
      omega
    nlinarith
  obtain ⟨g1d, g1⟩ := Cop.group_choice d (r / 2) Q hd hQ0 (hsize _ (by omega))
  obtain ⟨g2d, g2⟩ := Cop.group_choice d r Q hd hQ0 (hsize _ (by omega))
  set m1 := ((4 * d - 1) * (r / 2) - 4 * d) / (4 * d * Q)
  set m2 := ((4 * d - 1) * r - 4 * d) / (4 * d * Q)
  let m : ℕ → ℕ := fun i => if i < d' then m1 - i else m2 - (i - d')
  have hget : ∀ i < d, (copS d d' r).getD i 1 = 1 + Q * m i := by
    intro i hi
    simp [copS, copQ, List.getD_eq_getElem?_getD, hi, m, m1, m2, Q, F, D]
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi => ?_⟩
  · rw [hget i hi]
    have hE : Even Q := even_iff_two_dvd.2 ⟨F * (r / (2 * F * D) + 1), by rw [hQ]; ring⟩
    exact (hE.mul_right (m i)).one_add
  · -- coprimality via the window lemma: all indices are ≤ D
    have hmD : ∀ k, m k ≤ D := by
      intro k
      have hm2 : m2 ≤ D := by
        apply Nat.div_le_of_le_mul
        have h2 : (4 * d - 1) * r - 4 * d ≤ 4 * d * r := by
          have : (4 * d - 1) * r ≤ 4 * d * r := Nat.mul_le_mul_right r (by omega)
          omega
        calc (4 * d - 1) * r - 4 * d ≤ 4 * d * r := h2
          _ ≤ 4 * d * (Q * D) := Nat.mul_le_mul_left _ hQD.le
          _ = 4 * d * Q * D := by ring
      have h12 : m1 ≤ m2 := Nat.div_le_div_right (by
        have : (4 * d - 1) * (r / 2) ≤ (4 * d - 1) * r := Nat.mul_le_mul_left _ (by omega)
        omega)
      simp only [m]; split_ifs
      · exact ((Nat.sub_le _ _).trans h12).trans hm2
      · exact (Nat.sub_le _ _).trans hm2
    have hval : ∀ k < d, 4 * d * (1 + Q * m k) ≤ (4 * d - 1) * (if k < d' then r / 2 else r) ∧
        (4 * d - 2) * (if k < d' then r / 2 else r) < 4 * d * (1 + Q * m k) := by
      intro k hk0
      simp only [m]
      split_ifs with hk
      · exact ⟨(g1 k (by omega)).2, (g1 k (by omega)).1⟩
      · exact ⟨(g2 (k - d') (by omega)).2, (g2 (k - d') (by omega)).1⟩
    have hlt : (4 * d - 1) * (r / 2) < (4 * d - 2) * r := by
      have e2 : (4 * d - 1) * (r / 2) * 2 = (4 * d - 1) * r := by
        rw [mul_assoc, Nat.div_mul_cancel hr]
      have hr0 : 0 < r := by
        have : 0 < 64 * d ^ 2 * F := by positivity
        omega
      have : (4 * d - 1) * r < 2 * ((4 * d - 2) * r) := by
        rw [← mul_assoc]; exact Nat.mul_lt_mul_of_pos_right (by omega) hr0
      omega
    have hne : m i ≠ m j := by
      intro heq
      have hvi := hval i hi
      have hvj := hval j hj
      rw [heq] at hvi
      by_cases hi' : i < d' <;> by_cases hj' : j < d'
      · dsimp only [m] at heq; rw [if_pos hi', if_pos hj'] at heq
        exact hij (by omega)
      · rw [if_pos hi'] at hvi; rw [if_neg hj'] at hvj; omega
      · rw [if_neg hi'] at hvi; rw [if_pos hj'] at hvj; omega
      · dsimp only [m] at heq; rw [if_neg hi', if_neg hj'] at heq
        exact hij (by omega)
    rw [hget i hi, hget j hj]
    exact IntMul.HvdH.coprime_window D Q (m i) (m j) (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) hne
      (by have := hmD i; omega) (by have := hmD j; omega)
  · rw [hget i hi]
    simp only [m]
    split_ifs with hk
    · exact g1 i (by omega)
    · exact g2 (i - d') (by omega)

lemma logT_add (q : Params) (hdh : q.dh ≤ q.K) (he : 1 ≤ q.e) : q.logT + q.dh = q.K * q.e := by
  have key : ∀ n, ((List.range n).map q.te).sum + min n q.dh = n * q.e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hte : q.te n = if n < q.dh then q.e - 1 else q.e := rfl
      rw [hte, add_mul, one_mul]
      split_ifs with h
      · have : min (n + 1) q.dh = min n q.dh + 1 := by omega
        omega
      · have : min (n + 1) q.dh = min n q.dh := by omega
        omega
  have := key q.K
  rw [min_eq_right hdh] at this
  exact this

lemma two_mul_le_pow (n : ℕ) (hn : 4 ≤ n) : 2 * n ≤ 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]; ring
    omega

lemma E_lower (N b L E B : ℕ) (hb : b = Nat.size N) (hN : 1 ≤ N) (hL : N ≤ b * L)
    (hE : 4 * L ≤ 2 ^ E) (hB : B = Nat.size b) : b + 1 < B + E := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.lt_size.2 (by simpa using hN)
  have h1 : 2 ^ (b - 1) ≤ N := Nat.lt_size.1 (by omega)
  have h2 : b < 2 ^ B := by rw [hB]; exact Nat.lt_size_self b
  have h3 : 2 ^ (b + 1) = 4 * 2 ^ (b - 1) := by
    rw [show b + 1 = (b - 1) + 2 by omega, pow_add]; ring
  have h4 : 2 ^ (b + 1) < 2 ^ (B + E) := by
    calc 2 ^ (b + 1) ≤ 4 * N := by omega
      _ ≤ 4 * (b * L) := by omega
      _ = b * (4 * L) := by ring
      _ ≤ b * 2 ^ E := Nat.mul_le_mul_left _ hE
      _ < 2 ^ B * 2 ^ E := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
      _ = 2 ^ (B + E) := by rw [pow_add]
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h4

/-- The source lengths of `mkParams K N`: `K` pairwise coprime positive odd numbers in the window
`((4K-2)/(4K)) 2^{te i} < s_i ≤ ((4K-1)/(4K)) 2^{te i}`. -/
theorem mkParams_s_spec (K : ℕ) (hK : 1 ≤ K) (N : ℕ)
    (hN : 2 ^ 2 ^ (K * (64 * K ^ 2 * (256 * K ^ 2).factorial) + 4) ≤ N) :
    (mkParams K N).s.length = K ∧ (mkParams K N).s.Pairwise Nat.Coprime ∧
    (∀ x ∈ (mkParams K N).s, 0 < x) ∧
    ∀ i < K, (4 * K - 2) * 2 ^ (mkParams K N).te i < 4 * K * (mkParams K N).s.getD i 1 ∧
      4 * K * (mkParams K N).s.getD i 1 ≤ (4 * K - 1) * 2 ^ (mkParams K N).te i := by
  set C := 64 * K ^ 2 * (256 * K ^ 2).factorial with hC
  set q := mkParams K N with hq
  have qK : q.K = K := rfl
  have qb : q.b = Nat.size N := rfl
  have qL : q.L = (N + q.b - 1) / q.b := rfl
  have qe : q.e = (Nat.clog 2 (4 * q.L) + K - 1) / K := rfl
  have qdh : q.dh = K * q.e - Nat.clog 2 (4 * q.L) := rfl
  have qs : q.s = copS K q.dh (2 ^ q.e) := rfl
  have qα : q.α = K * (ceilSqrt (ceilSqrt q.b) + 2) := rfl
  have qp : q.p = 2 * q.b + 2 * Nat.clog 2 (4 * q.L) + 6 * K * q.α ^ 2 + 8 * Nat.size q.b + 4 * K + 64 := rfl
  have qP : q.P = 2 * q.p + Nat.clog 2 (4 * q.L) + 8 := rfl
  have qfn : q.fn = 4 * q.r * q.P := rfl
  set b := q.b with hb
  set L := q.L with hLdef
  set E := Nat.clog 2 (4 * L) with hEdef
  set B := Nat.size b with hBdef
  set c := ceilSqrt (ceilSqrt b) with hcdef
  -- sizes
  have hC64 : 64 ≤ C := by
    have := Nat.factorial_pos (256 * K ^ 2)
    have : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK
    rw [hC]; nlinarith
  have hKC : K ≤ K * C := Nat.le_mul_of_pos_right K (by omega)
  have hbig1 : 2 ^ (K * C + 4) < b := by rw [qb]; exact Nat.lt_size.2 hN
  have hB : K * C + 4 < B := Nat.lt_size.2 hbig1.le
  have hNpos : 1 ≤ N := le_trans Nat.one_le_two_pow hN
  have hb1 : 1 ≤ b := lt_of_le_of_lt (Nat.zero_le _) hbig1
  have hbB : 2 ^ (B - 1) ≤ b := Nat.lt_size.1 (by omega)
  have hbB' : b < 2 ^ B := Nat.lt_size_self b
  have hNb : N < 2 ^ b := by rw [qb]; exact Nat.lt_size_self N
  have hBb : B ≤ b := Nat.size_le.2 Nat.lt_two_pow_self
  have hbb : b < 2 ^ b := Nat.lt_two_pow_self
  -- L
  have hNbL : N ≤ b * L := by
    have h := Nat.lt_mul_div_succ (N + b - 1) (show 0 < b by omega)
    rw [qL]
    rw [mul_add, mul_one] at h
    omega
  have hL1 : 1 ≤ L := by
    rw [qL]
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hLb : L * b ≤ N + b - 1 := by rw [qL]; exact Nat.div_mul_le_self _ _
  have hLle : L ≤ N + b := by
    have : L ≤ L * b := Nat.le_mul_of_pos_right L (by omega)
    omega
  -- E
  have hE4 : 4 * L ≤ 2 ^ E := Nat.le_pow_clog (by norm_num) _
  have hEle : E ≤ b + 3 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]; omega
  have hElow := E_lower N b L E B qb hNpos hNbL hE4 rfl
  have h2B : 2 * B ≤ 2 ^ (B - 1) := two_mul_le_pow B (by omega)
  have hEC : K * C + 6 ≤ E := by omega
  -- e and dh
  have he' : q.e = (E + K - 1) / K := qe
  have hKe1 : E ≤ K * q.e := by
    have h := Nat.lt_mul_div_succ (E + K - 1) (show 0 < K by omega)
    rw [he']; rw [mul_add, mul_one] at h; omega
  have hKe2 : K * q.e ≤ E + K - 1 := by rw [he']; exact Nat.mul_div_le _ _
  have hdh : q.dh < K := by rw [qdh]; omega
  have heC : C ≤ q.e := by
    have : K * C ≤ K * q.e := by omega
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have he2 : 2 ≤ q.e := by omega
  have hbig : 64 * K ^ 2 * (256 * K ^ 2).factorial ≤ 2 ^ q.e :=
    le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) heC)
  have hlogT : q.logT = E := by
    have := logT_add q (by rw [qK]; omega) (by omega)
    rw [qK, qdh] at this
    omega
  -- the source lengths
  obtain ⟨hodd, hcop, hsb⟩ := copS_spec K q.dh (2 ^ q.e) hK hdh.le (dvd_pow_self 2 (by omega)) hbig
  have hte : ∀ i, 2 ^ q.te i = if i < q.dh then 2 ^ q.e / 2 else 2 ^ q.e := by
    intro i
    unfold Params.te
    split_ifs
    · rw [show 2 ^ q.e = 2 * 2 ^ (q.e - 1) by rw [← pow_succ']; congr 1; omega]
      simp
    · rfl
  have hlen : q.s.length = K := by rw [qs]; simp [copS]
  have hget : ∀ i (h : i < q.s.length), q.s[i] = q.s.getD i 1 := by
    intro i h; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  refine ⟨hlen, ?_, ?_, fun i hi => by rw [hte i, qs]; exact hsb i hi⟩
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [hget i hi, hget j hj, qs]
    exact hcop i (hlen ▸ hi) j (hlen ▸ hj) (Nat.ne_of_lt hij)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [hget i hi]
    have := hodd i (hlen ▸ hi)
    rw [← qs] at this
    exact this.pos

end IntMul.HvdH.RefPf

end

open IntMul.HvdH IntMul.HvdH.Ref

theorem solution (K : ℕ) (hK : 1 ≤ K) (N : ℕ)
    (hN : 2 ^ 2 ^ (K * (64 * K ^ 2 * (256 * K ^ 2).factorial) + 4) ≤ N) :
    (mkParams K N).s.length = K ∧ (mkParams K N).s.Pairwise Nat.Coprime ∧
    (∀ x ∈ (mkParams K N).s, 0 < x) ∧
    ∀ i < K, (4 * K - 2) * 2 ^ (mkParams K N).te i < 4 * K * (mkParams K N).s.getD i 1 ∧
      4 * K * (mkParams K N).s.getD i 1 ≤ (4 * K - 1) * 2 ^ (mkParams K N).te i :=
  IntMul.HvdH.RefPf.mkParams_s_spec K hK N hN
