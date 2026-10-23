-- Prove2me | solution 1 for NeedPersuasion.FirstBest.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:33:01.043629+00:00
-- url     : https://prove2.me/submissions/7125ff19-e29d-49eb-83ca-1c87ee221c69

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model

set_option autoImplicit false

namespace NPFBT2Aux
open NeedPersuasion.FirstBest

theorem ev_summ {F G : ℕ → ℝ} (K : ℕ) (r : ℝ) (hG : Summable G)
    (h : ∀ n, K ≤ n → F n = r * G n) : Summable F := by
  apply (summable_nat_add_iff K).mp
  exact (((summable_nat_add_iff K).mpr hG).mul_left r).congr
    (fun n => (h (n+K) (Nat.le_add_left K n)).symm)

theorem tsum_shiftC {E f : ℕ → ℝ} (hE : Summable E) (hEf : Summable (fun n => E n * f n))
    (h0 : ∑' n, E n = 0) (C : ℝ) : ∑' n, E n * f n = ∑' n, E n * (f n - C) := by
  have : (fun n => E n * (f n - C)) = fun n => E n * f n - C * E n := by ext n; ring
  rw [this, hEf.tsum_sub (hE.mul_left C), tsum_mul_left, h0]; ring

theorem sbp {D g : ℕ → ℝ} (hD0 : D 0 = 0) (hs : Summable (fun n => D (n+1) * g n)) :
    ∑' n, D (n+1) * g n = ∑' n, D n * g (n - 1) := by
  have h1 : HasSum (fun n => (fun n => D n * g (n - 1)) (n + 1))
      (∑' n, D (n+1) * g n - ∑ i ∈ Finset.range 1, (fun n => D n * g (n - 1)) i) := by
    simpa [hD0] using hs.hasSum
  exact ((hasSum_nat_add_iff' 1).mp h1).tsum_eq.symm

section
variable {M : Model}

theorem succ_zero {π : ℕ → ℝ} (h : π ∈ PiAP M) (n : ℕ) (h0 : π n = 0) : π (n+1) = 0 := by
  obtain ⟨hnn, -, hr, -, -⟩ := h
  have h1 := (hr n).2
  have h2 := hnn (n+1)
  rw [h0, mul_zero] at h1
  linarith

theorem zero_add_of {π : ℕ → ℝ} (h : π ∈ PiAP M) (n : ℕ) (h0 : π n = 0) :
    ∀ j, π (n+j) = 0 := by
  intro j
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [← add_assoc]; exact succ_zero h _ ih

theorem pos_of_le {π : ℕ → ℝ} (h : π ∈ PiAP M) {n m : ℕ} (hnm : n ≤ m) (hm : 0 < π m) :
    0 < π n := by
  rcases (h.1 n).lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have := zero_add_of h n h1.symm (m - n)
    rw [Nat.add_sub_cancel' hnm] at this
    linarith

theorem pi0_pos {π : ℕ → ℝ} (h : π ∈ PiAP M) : 0 < π 0 := by
  rcases (h.1 0).lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have hz : ∀ j, π j = 0 := fun j => by simpa using zero_add_of h 0 h1.symm j
    have h3 : HasSum π 0 := by
      have : π = fun _ => 0 := funext hz
      rw [this]; exact hasSum_zero
    have := h3.unique h.2.1
    norm_num at this

theorem summ_shift (hM : M.Standing) {π : ℕ → ℝ} (h : π ∈ PiAP M) :
    Summable (fun n => π (n+1) * M.uL n) := by
  obtain ⟨hnn, hs, -, hsL, -⟩ := h
  have hanti : StrictAnti M.uL := hM.2.2.2.2.2.2.2.1
  have h1 : Summable (fun n => |M.uL 0| * π (n+1) + |π (n+1) * M.uL (n+1)|) :=
    (((summable_nat_add_iff 1).mpr hs.summable).mul_left _).add
      ((summable_nat_add_iff 1).mpr hsL).abs
  refine Summable.of_norm_bounded h1 (fun n => ?_)
  have hle1 : M.uL (n+1) ≤ M.uL n := (hanti (Nat.lt_succ_self n)).le
  have hle0 : M.uL n ≤ M.uL 0 := hanti.antitone (Nat.zero_le n)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hnn _)]
  have : |M.uL n| ≤ |M.uL 0| + |M.uL (n+1)| := by
    rcases le_or_gt 0 (M.uL n) with h | h
    · rw [abs_of_nonneg h]
      have := le_abs_self (M.uL 0); have := abs_nonneg (M.uL (n+1)); linarith
    · rw [abs_of_neg h]
      have := neg_abs_le (M.uL (n+1)); have := abs_nonneg (M.uL 0); linarith
  have hp := hnn (n+1)
  nlinarith

theorem WLsum (hM : M.Standing) {π : ℕ → ℝ} (h : π ∈ PiAP M) :
    Summable (fun n => (π (n+1) - M.lamH * π n) * M.uL n) :=
  ((summ_shift hM h).sub (h.2.2.2.1.mul_left M.lamH)).congr (fun n => by ring)

theorem Lsum (hM : M.Standing) {π : ℕ → ℝ} (h : π ∈ PiAP M) :
    Summable (fun n => (M.lam * π n - π (n+1)) * M.uL n) :=
  ((h.2.2.2.1.mul_left M.lam).sub (summ_shift hM h)).congr (fun n => by ring)

theorem WL_add (hM : M.Standing) {π D : ℕ → ℝ} (h : π ∈ PiAP M)
    (hDL : Summable (fun n => D n * M.uL n)) (hDL1 : Summable (fun n => D (n+1) * M.uL n)) :
    WL M (fun n => π n + D n) = WL M π + ∑' n, (D (n+1) - M.lamH * D n) * M.uL n := by
  unfold WL
  rw [← (WLsum hM h).tsum_add ((hDL1.sub (hDL.mul_left M.lamH)).congr (fun n => by ring))]
  congr 1; ext n; ring

theorem leave_add (hM : M.Standing) {π D : ℕ → ℝ} (h : π ∈ PiAP M)
    (hDL : Summable (fun n => D n * M.uL n)) (hDL1 : Summable (fun n => D (n+1) * M.uL n)) :
    leaveVal M (fun n => π n + D n) =
      leaveVal M π + ∑' n, (M.lam * D n - D (n+1)) * M.uL n := by
  unfold leaveVal
  rw [← (Lsum hM h).tsum_add (((hDL.mul_left M.lam).sub hDL1).congr (fun n => by ring))]
  congr 1; ext n; ring

theorem WH_add {π D : ℕ → ℝ} (h : π ∈ PiAP M) (hDH : Summable (fun n => D n * M.uH n)) :
    WH M (fun n => π n + D n) = WH M π + M.lamH * ∑' n, D n * M.uH n := by
  unfold WH
  rw [← mul_add, ← h.2.2.2.2.tsum_add hDH]
  congr 2; ext n; ring

set_option maxHeartbeats 1000000 in
theorem exch1AP (hM : M.Standing) {π : ℕ → ℝ} (hπ : π ∈ PiAP M) (k : ℕ)
    (hu : π (k+1) < M.lam * π k) (hd : M.lamH * π (k+1) < π (k+2)) :
    ∃ π' ∈ PiAP M, Dominates M π' π := by
  have hAP : π ∈ PiAP M := hπ
  obtain ⟨hnn, hs, hr, hsL, hsH⟩ := hAP
  have hM' := hM
  obtain ⟨hlL, hlH, hl1, -, -, -, -, hL, hH, hΔ⟩ := hM'
  have hl : M.lam = M.lamL + M.lamH := rfl
  have hlH1 : M.lamH ≤ 1 := by linarith
  have hl0 : 0 ≤ M.lam := by linarith
  have hTs : Summable (fun n => π (n + (k+2))) := (summable_nat_add_iff (k+2)).mpr hs.summable
  obtain ⟨T, hT⟩ : ∃ T, T = ∑' n, π (n + (k+2)) := ⟨_, rfl⟩
  have hT1 : π (k+2) ≤ T := by
    have := hTs.le_tsum 0 (fun j _ => hnn _)
    simpa [hT] using this
  have hp1 := hnn (k+1)
  have hp2 : 0 < π (k+2) := by nlinarith
  have hTpos : 0 < T := by linarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = min (M.lam * π k - π (k+1)) ((π (k+2) - M.lamH * π (k+1)) / 2) :=
    ⟨_, rfl⟩
  have hs1 : s ≤ M.lam * π k - π (k+1) := by rw [hsdef]; exact min_le_left _ _
  have hs2 : s ≤ (π (k+2) - M.lamH * π (k+1)) / 2 := by rw [hsdef]; exact min_le_right _ _
  have hs0 : 0 < s := by rw [hsdef]; exact lt_min (by linarith) (by linarith)
  obtain ⟨r, hrdef⟩ : ∃ r, r = s / T := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrT : r * T = s := by rw [hrdef]; field_simp
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one hTpos]
    have : 0 ≤ M.lamH * π (k+1) := mul_nonneg hlH hp1
    linarith
  have hrp2 : r * π (k+2) ≤ s := by rw [← hrT]; exact mul_le_mul_of_nonneg_left hT1 hr0.le
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ,
      D = fun n => if n = k+1 then s else if k+2 ≤ n then -r * π n else 0 := ⟨_, rfl⟩
  have hDk1 : D (k+1) = s := by simp [hD]
  have hDle : ∀ n, n ≤ k → D n = 0 := by
    intro n hn; simp only [hD]
    rw [if_neg (show ¬ n = k+1 by omega), if_neg (show ¬ k+2 ≤ n by omega)]
  have hDge : ∀ n, k+2 ≤ n → D n = -r * π n := by
    intro n hn; simp only [hD]
    rw [if_neg (show ¬ n = k+1 by omega), if_pos hn]
  have hDsum : HasSum D 0 := by
    have h1 : HasSum (fun n => if n = k+1 then s else 0) s := hasSum_ite_eq (k+1) s
    have hz : ∑ i ∈ Finset.range (k+2), (if k+2 ≤ i then -r * π i else 0) = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      rw [Finset.mem_range] at hi; rw [if_neg (by omega)]
    have h4 : HasSum (fun n => (fun n => if k+2 ≤ n then -r * π n else 0) (n + (k+2)))
        (-r * T - ∑ i ∈ Finset.range (k+2), (if k+2 ≤ i then -r * π i else 0)) := by
      rw [hz, sub_zero, hT]
      simpa using hTs.hasSum.mul_left (-r)
    have h2 := (hasSum_nat_add_iff' (f := fun n => if k+2 ≤ n then -r * π n else 0) (k+2)).mp h4
    have h3 := h1.add h2
    rw [show s + -r * T = 0 by linarith [hrT]] at h3
    convert h3 using 1
    ext n; simp only [hD]
    by_cases h : n = k+1
    · subst h; simp
    · rw [if_neg h, if_neg h, zero_add]
  have hDf : ∀ f : ℕ → ℝ, Summable (fun n => π n * f n) → Summable (fun n => D n * f n) := by
    intro f hf
    exact ev_summ (k+2) (-r) hf (fun n hn => by rw [hDge n hn]; ring)
  have hDL1 : Summable (fun n => D (n+1) * M.uL n) :=
    ev_summ (k+2) (-r) (summ_shift hM hπ) (fun n hn => by rw [hDge (n+1) (by omega)]; ring)
  have hDL : Summable (fun n => D n * M.uL n) := hDf _ hsL
  have hDH : Summable (fun n => D n * M.uH n) := hDf _ hsH
  have hDs : Summable D := hDsum.summable
  have hD0 : D 0 = 0 := hDle 0 (Nat.zero_le _)
  have hDtsum : ∑' n, D n = 0 := hDsum.tsum_eq
  have hD1tsum : ∑' n, D (n+1) = 0 := by
    have := ((hasSum_nat_add_iff' 1).mpr hDsum).tsum_eq
    simpa [hD0] using this
  have hcase : ∀ n, n ≤ k ∨ n = k+1 ∨ k+2 ≤ n := by intro n; omega
  have h1r : 0 ≤ 1 - r := by linarith
  -- the perturbed mechanism is an admission policy
  have hAP' : (fun n => π n + D n) ∈ PiAP M := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n
      rcases hcase n with h | h | h
      · show 0 ≤ π n + D n
        rw [hDle n h]; simpa using hnn n
      · show 0 ≤ π n + D n
        rw [h, hDk1]; linarith
      · show 0 ≤ π n + D n
        rw [hDge n h]; nlinarith [hnn n]
    · simpa using hs.add hDsum
    · intro n
      show M.lamH * (π n + D n) ≤ π (n+1) + D (n+1) ∧ π (n+1) + D (n+1) ≤ M.lam * (π n + D n)
      rcases (show n < k ∨ n = k ∨ n = k+1 ∨ k+2 ≤ n by omega) with h | h | h | h
      · rw [hDle n h.le, hDle (n+1) h]; simpa using hr n
      · subst h
        rw [hDle n le_rfl, hDk1]
        have := (hr n).1
        constructor <;> linarith
      · subst h
        rw [hDk1, hDge (k+1+1) (by omega)]
        show M.lamH * (π (k+1) + s) ≤ π (k+2) + -r * π (k+2) ∧
          π (k+2) + -r * π (k+2) ≤ M.lam * (π (k+1) + s)
        have h12 : π (k+2) ≤ M.lam * π (k+1) := (hr (k+1)).2
        have hls : M.lamH * s ≤ s := by nlinarith
        have hrp : 0 ≤ r * π (k+2) := by positivity
        have hlss : 0 ≤ M.lam * s := by positivity
        constructor <;> nlinarith
      · rw [hDge n h, hDge (n+1) (by omega)]
        have e1 := mul_le_mul_of_nonneg_left (hr n).1 h1r
        have e2 := mul_le_mul_of_nonneg_left (hr n).2 h1r
        constructor <;> nlinarith
    · exact (hsL.add (hDf _ hsL)).congr (fun n => by ring)
    · exact (hsH.add (hDf _ hsH)).congr (fun n => by ring)
  -- low-need welfare strictly increases
  have hEs : Summable (fun n => D (n+1)) := (summable_nat_add_iff 1).mpr hDs
  have hE : Summable (fun n => D (n+1) - M.lamH * D n) := hEs.sub (hDs.mul_left _)
  have hE0 : ∑' n, (D (n+1) - M.lamH * D n) = 0 := by
    rw [hEs.tsum_sub (hDs.mul_left _), tsum_mul_left, hD1tsum, hDtsum]; ring
  have hEL : Summable (fun n => (D (n+1) - M.lamH * D n) * M.uL n) :=
    (hDL1.sub (hDL.mul_left M.lamH)).congr (fun n => by ring)
  have hWL : WL M (fun n => π n + D n) =
      WL M π + ∑' n, (D (n+1) - M.lamH * D n) * (M.uL n - M.uL (k+1)) := by
    rw [WL_add hM hπ hDL hDL1, tsum_shiftC hE hEL hE0 (M.uL (k+1))]
  have hX : 0 < ∑' n, (D (n+1) - M.lamH * D n) * (M.uL n - M.uL (k+1)) := by
    refine Summable.tsum_pos ((hEL.sub (hE.mul_left (M.uL (k+1)))).congr (fun n => by ring)) ?_ k ?_
    · intro n
      rcases (show n < k ∨ n = k ∨ n = k+1 ∨ k+2 ≤ n by omega) with h | h | h | h
      · rw [hDle n h.le, hDle (n+1) h]; simp
      · rw [h, hDle k le_rfl, hDk1]
        have := hL (show k < k+1 by omega)
        nlinarith
      · rw [h]; simp
      · rw [hDge n h, hDge (n+1) (by omega)]
        have := mul_nonneg (mul_nonneg hr0.le (sub_nonneg.mpr (hr n).1))
          (sub_nonneg.mpr (hL.antitone (show k+1 ≤ n by omega)))
        exact this.trans_eq (by ring)
    · rw [hDle k le_rfl, hDk1]
      have := hL (show k < k+1 by omega)
      simp only [mul_zero, sub_zero]
      exact mul_pos hs0 (sub_pos.mpr this)
  -- high-need welfare weakly increases
  have hWH : WH M (fun n => π n + D n) =
      WH M π + M.lamH * ∑' n, D n * (M.uH n - M.uH (k+1)) := by
    rw [WH_add hπ hDH, tsum_shiftC hDs hDH hDtsum (M.uH (k+1))]
  have hZ : 0 ≤ ∑' n, D n * (M.uH n - M.uH (k+1)) := by
    apply tsum_nonneg; intro n
    rcases hcase n with h | h | h
    · rw [hDle n h]; simp
    · rw [h]; simp
    · rw [hDge n h]
      have := mul_nonneg (mul_nonneg hr0.le (hnn n))
        (sub_nonneg.mpr (hH.antitone (show k+1 ≤ n by omega)))
      exact this.trans_eq (by ring)
  -- LEAVE stays satisfied
  have hHs : Monotone (fun j => M.lam * M.uL (j+1) - M.uL j) := by
    apply monotone_nat_of_le_succ; intro i
    have h1 : M.uL (i+1) - M.uL (i+1+1) ≤ M.uL i - M.uL (i+1) := hΔ (Nat.le_succ i)
    have h2 : M.uL (i+1+1) < M.uL (i+1) := hL (by omega)
    show M.lam * M.uL (i+1) - M.uL i ≤ M.lam * M.uL (i+1+1) - M.uL (i+1)
    have h3 : 0 ≤ 1 - M.lam := by linarith
    nlinarith [mul_nonneg h3 (sub_nonneg.mpr h2.le)]
  have hDg : Summable (fun n => D n * M.uL (n-1)) :=
    (summable_nat_add_iff 1).mp (hDL1.congr (fun n => by simp))
  have hLeq : leaveVal M (fun n => π n + D n) = leaveVal M π +
      ∑' n, D n * ((M.lam * M.uL n - M.uL (n-1)) - (M.lam * M.uL (k+1) - M.uL k)) := by
    rw [leave_add hM hπ hDL hDL1]
    congr 1
    have hsplit : ∑' n, (M.lam * D n - D (n+1)) * M.uL n =
        ∑' n, D n * (M.lam * M.uL n - M.uL (n-1)) := by
      rw [show (fun n => (M.lam * D n - D (n+1)) * M.uL n) =
          fun n => M.lam * (D n * M.uL n) - D (n+1) * M.uL n by ext; ring]
      rw [(hDL.mul_left _).tsum_sub hDL1, tsum_mul_left, sbp hD0 hDL1]
      rw [show (fun n => D n * (M.lam * M.uL n - M.uL (n-1))) =
          fun n => M.lam * (D n * M.uL n) - D n * M.uL (n-1) by ext; ring]
      rw [(hDL.mul_left _).tsum_sub hDg, tsum_mul_left]
    rw [hsplit]
    exact tsum_shiftC hDs (((hDL.mul_left M.lam).sub hDg).congr (fun n => by ring)) hDtsum _
  have hY : ∑' n, D n * ((M.lam * M.uL n - M.uL (n-1)) - (M.lam * M.uL (k+1) - M.uL k)) ≤ 0 := by
    apply tsum_nonpos; intro n
    rcases hcase n with h | h | h
    · rw [hDle n h]; simp
    · rw [h]; simp
    · rw [hDge n h]
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n-1, by omega⟩
      have hmono : M.lam * M.uL (k+1) - M.uL k ≤ M.lam * M.uL (j+1) - M.uL j :=
        hHs (show k ≤ j by omega)
      simp only [Nat.add_sub_cancel]
      have := mul_nonneg (mul_nonneg hr0.le (hnn (j+1))) (sub_nonneg.mpr hmono)
      exact (neg_nonpos.mpr this).trans_eq' (by ring)
  refine ⟨fun n => π n + D n, hAP', ⟨⟨?_, ?_⟩, Or.inl ?_⟩⟩
  · rw [hWL]; linarith
  · rw [hWH]; nlinarith [mul_nonneg hlH hZ]
  · rw [hWL]; linarith

set_option maxHeartbeats 1000000 in
theorem exch2AP (hM : M.Standing) {π : ℕ → ℝ} (hπ : π ∈ PiAP M) (N : ℕ)
    (hneg : ∀ n, N ≤ n → M.uL n < 0) (hpos : ∀ n, n < N → 0 ≤ M.uL n)
    (hup : ∀ j, j < N → π (j+1) = M.lam * π j)
    (hd : M.lamH * π N < π (N+1)) : ∃ π' ∈ PiAP M, Dominates M π' π := by
  have hAP : π ∈ PiAP M := hπ
  have h00 := pi0_pos hAP
  obtain ⟨hnn, hs, hr, hsL, hsH⟩ := hAP
  have hM' := hM
  obtain ⟨hlL, hlH, hl1, -, -, -, -, hL, hH, hΔ⟩ := hM'
  have hl : M.lam = M.lamL + M.lamH := rfl
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ i ∈ Finset.range (N+1), π i := ⟨_, rfl⟩
  have hA0 : 0 < A := by
    rw [hA]
    exact lt_of_lt_of_le h00
      (Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_range.mpr (Nat.succ_pos N)))
  have hA1 : A ≤ 1 := by rw [hA]; exact sum_le_hasSum _ (fun i _ => hnn i) hs
  have hpN1 : 0 < π (N+1) := by nlinarith [hnn N]
  obtain ⟨c, hc⟩ : ∃ c, c = M.lamH * π N / π (N+1) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg (mul_nonneg hlH (hnn N)) hpN1.le
  have hc1 : c < 1 := by rw [hc, div_lt_one hpN1]; exact hd
  have hcπ : c * π (N+1) = M.lamH * π N := by rw [hc]; field_simp
  obtain ⟨S, hS⟩ : ∃ S, S = c + (1 - c) * A := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [hS]; nlinarith
  have hS1 : S ≤ 1 := by rw [hS]; nlinarith
  have hcS : c < S := by rw [hS]; nlinarith
  obtain ⟨a, ha⟩ : ∃ a, a = 1 / S - 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = c / S - 1 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha, sub_nonneg, le_div_iff₀ hS0]; linarith
  have hb0 : b < 0 := by rw [hb, sub_neg, div_lt_one hS0]; exact hcS
  have hb1 : 0 ≤ 1 + b := by
    rw [hb]; have : 0 ≤ c / S := div_nonneg hc0 hS0.le
    linarith
  have hkey : (1 + b) * π (N+1) = (1 + a) * (M.lamH * π N) := by
    rw [ha, hb, ← hcπ]; ring
  have hbal : a * A + b * (1 - A) = 0 := by
    have hSne : S ≠ 0 := hS0.ne'
    rw [ha, hb]; field_simp; rw [hS]; ring
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, D = fun n => if n ≤ N then a * π n else b * π n := ⟨_, rfl⟩
  have hDle : ∀ n, n ≤ N → D n = a * π n := by
    intro n hn; simp only [hD]; rw [if_pos hn]
  have hDgt : ∀ n, N < n → D n = b * π n := by
    intro n hn; simp only [hD]; rw [if_neg (show ¬ n ≤ N by omega)]
  have hDsum : HasSum D 0 := by
    have h1 : HasSum (fun n => b * π n) (b * 1) := hs.mul_left b
    have h2 : HasSum (fun n => if n ≤ N then (a - b) * π n else 0)
        (∑ i ∈ Finset.range (N+1), if i ≤ N then (a - b) * π i else 0) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by
        rw [Finset.mem_range] at hn; rw [if_neg (show ¬ n ≤ N by omega)])
    have h3 : ∑ i ∈ Finset.range (N+1), (if i ≤ N then (a - b) * π i else 0) = (a - b) * A := by
      rw [hA, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_range] at hi; rw [if_pos (show i ≤ N by omega)]
    have h4 := h1.add h2
    rw [h3, show b * 1 + (a - b) * A = 0 by linear_combination hbal] at h4
    convert h4 using 1
    ext n; simp only [hD]; split_ifs <;> ring
  have hDf : ∀ f : ℕ → ℝ, Summable (fun n => π n * f n) → Summable (fun n => D n * f n) := by
    intro f hf
    exact ev_summ (N+1) b hf (fun n hn => by rw [hDgt n (by omega)]; ring)
  have hDL1 : Summable (fun n => D (n+1) * M.uL n) :=
    ev_summ (N+1) b (summ_shift hM hπ) (fun n hn => by rw [hDgt (n+1) (by omega)]; ring)
  have hDL : Summable (fun n => D n * M.uL n) := hDf _ hsL
  have hDH : Summable (fun n => D n * M.uH n) := hDf _ hsH
  have hDs : Summable D := hDsum.summable
  have hDtsum : ∑' n, D n = 0 := hDsum.tsum_eq
  have hlHl : M.lamH ≤ M.lam := by linarith
  have h1a : 0 ≤ 1 + a := by linarith
  have hAP' : (fun n => π n + D n) ∈ PiAP M := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n
      show 0 ≤ π n + D n
      rcases le_or_gt n N with h | h
      · rw [hDle n h]; nlinarith [hnn n]
      · rw [hDgt n h]; nlinarith [hnn n]
    · simpa using hs.add hDsum
    · intro n
      show M.lamH * (π n + D n) ≤ π (n+1) + D (n+1) ∧ π (n+1) + D (n+1) ≤ M.lam * (π n + D n)
      rcases (show n < N ∨ n = N ∨ N < n by omega) with h | h | h
      · rw [hDle n h.le, hDle (n+1) h]
        have e1 := mul_le_mul_of_nonneg_left (hr n).1 h1a
        have e2 := mul_le_mul_of_nonneg_left (hr n).2 h1a
        constructor <;> nlinarith
      · subst h
        rw [hDle n le_rfl, hDgt (n+1) (by omega)]
        have e3 : 0 ≤ (1 + a) * π n := mul_nonneg h1a (hnn n)
        have e4 := mul_le_mul_of_nonneg_right hlHl e3
        constructor <;> nlinarith
      · rw [hDgt n h, hDgt (n+1) (by omega)]
        have e1 := mul_le_mul_of_nonneg_left (hr n).1 hb1
        have e2 := mul_le_mul_of_nonneg_left (hr n).2 hb1
        constructor <;> nlinarith
    · exact (hsL.add (hDf _ hsL)).congr (fun n => by ring)
    · exact (hsH.add (hDf _ hsH)).congr (fun n => by ring)
  have hEL : Summable (fun n => (D (n+1) - M.lamH * D n) * M.uL n) :=
    (hDL1.sub (hDL.mul_left M.lamH)).congr (fun n => by ring)
  have hWL := WL_add hM hπ hDL hDL1
  have hX : 0 < ∑' n, (D (n+1) - M.lamH * D n) * M.uL n := by
    refine Summable.tsum_pos hEL ?_ N ?_
    · intro n
      rcases (show n < N ∨ n = N ∨ N < n by omega) with h | h | h
      · rw [hDle n h.le, hDle (n+1) h]
        have := mul_nonneg (mul_nonneg ha0 (sub_nonneg.mpr (hr n).1)) (hpos n h)
        exact this.trans_eq (by ring)
      · rw [h, hDle N le_rfl, hDgt (N+1) (by omega)]
        have e : b * π (N+1) - M.lamH * (a * π N) = M.lamH * π N - π (N+1) := by
          linear_combination hkey
        rw [e]
        exact (mul_pos_of_neg_of_neg (by linarith) (hneg N le_rfl)).le
      · rw [hDgt n h, hDgt (n+1) (by omega)]
        have := mul_nonneg (mul_nonneg (neg_nonneg.mpr hb0.le) (sub_nonneg.mpr (hr n).1))
          (neg_nonneg.mpr (hneg n h.le).le)
        exact this.trans_eq (by ring)
    · rw [hDle N le_rfl, hDgt (N+1) (by omega)]
      have e : b * π (N+1) - M.lamH * (a * π N) = M.lamH * π N - π (N+1) := by
        linear_combination hkey
      rw [e]
      exact mul_pos_of_neg_of_neg (by linarith) (hneg N le_rfl)
  have hWH : WH M (fun n => π n + D n) =
      WH M π + M.lamH * ∑' n, D n * (M.uH n - M.uH N) := by
    rw [WH_add hπ hDH, tsum_shiftC hDs hDH hDtsum (M.uH N)]
  have hZ : 0 ≤ ∑' n, D n * (M.uH n - M.uH N) := by
    apply tsum_nonneg; intro n
    rcases le_or_gt n N with h | h
    · rw [hDle n h]
      have := mul_nonneg (mul_nonneg ha0 (hnn n)) (sub_nonneg.mpr (hH.antitone h))
      exact this.trans_eq (by ring)
    · rw [hDgt n h]
      have := mul_nonneg (mul_nonneg (neg_nonneg.mpr hb0.le) (hnn n))
        (sub_nonneg.mpr (hH.antitone h.le))
      exact this.trans_eq (by ring)
  have hLv : leaveVal M (fun n => π n + D n) ≤ 0 := by
    show ∑' n, (M.lam * (π n + D n) - (π (n+1) + D (n+1))) * M.uL n ≤ 0
    apply tsum_nonpos; intro n
    rcases lt_or_ge n N with h | h
    · rw [hDle n h.le, hDle (n+1) h, hup n h]
      apply le_of_eq; ring
    · have h1 : π (n+1) + D (n+1) ≤ M.lam * (π n + D n) := (hAP'.2.2.1 n).2
      have h2 := hneg n h
      exact mul_nonpos_iff.mpr (Or.inl ⟨by linarith, h2.le⟩)
  refine ⟨fun n => π n + D n, hAP', ⟨⟨?_, ?_⟩, Or.inl ?_⟩⟩
  · rw [hWL]; linarith
  · rw [hWH]; nlinarith [mul_nonneg hlH hZ]
  · rw [hWL]; linarith

theorem mainAP (M : Model) (hM : M.Standing) (π : ℕ → ℝ)
    (hπ : ParetoEfficientIn M (PiAP M) π) :
    HasThresholdStructure M π ∧ HasThresholdAtMost M π (mfi M) := by
  obtain ⟨hSM, hnd⟩ := hπ
  have hAP : π ∈ PiAP M := hSM
  have h00 := pi0_pos hAP
  obtain ⟨hnn, hs, hr, -, -⟩ := hAP
  have hM' := hM
  obtain ⟨hlL, hlH, hl1, -, -, hne, -, hL, -, -⟩ := hM'
  have hl : M.lam = M.lamL + M.lamH := rfl
  have noAdj : ∀ k, π (k+1) < M.lam * π k → M.lamH * π (k+1) < π (k+2) → False := by
    intro k h1 h2
    obtain ⟨π', h', hdom⟩ := exch1AP hM hSM k h1 h2
    exact hnd π' h' hdom
  obtain ⟨N, hNdef⟩ : ∃ N, N = mfi M := ⟨_, rfl⟩
  have hNneg : M.uL N < 0 := by rw [hNdef]; exact Nat.sInf_mem hne
  have hneg : ∀ n, N ≤ n → M.uL n < 0 := fun n hn => lt_of_le_of_lt (hL.antitone hn) hNneg
  have hpos : ∀ n, n < N → 0 ≤ M.uL n := by
    intro n hn; rw [hNdef] at hn
    exact not_lt.mp (Nat.notMem_of_lt_sInf (s := {k | M.uL k < 0}) hn)
  have noDown : (∀ j, j < N → π (j+1) = M.lam * π j) → M.lamH * π N < π (N+1) → False := by
    intro hup hd
    obtain ⟨π', h', hdom⟩ := exch2AP hM hSM N hneg hpos hup hd
    exact hnd π' h' hdom
  have hAt : HasThresholdAtMost M π (mfi M) := by
    rw [← hNdef]
    by_cases hex : ∃ k, π (k+1) < M.lam * π k
    · classical
      obtain ⟨m, hm, hmin⟩ : ∃ m, π (m+1) < M.lam * π m ∧
          ∀ k, k < m → π (k+1) = M.lam * π k :=
        ⟨Nat.find hex, Nat.find_spec hex,
          fun k hk => le_antisymm (hr k).2 (not_lt.mp (Nat.find_min hex hk))⟩
      have claim : ∀ j, m ≤ j → π (j+1) < M.lam * π j ∨ π j = 0 := by
        intro j hj
        induction j, hj using Nat.le_induction with
        | base => exact Or.inl hm
        | succ j hj ih =>
          rcases ih with h | h
          · have he : π (j+1+1) = M.lamH * π (j+1) :=
              le_antisymm (not_lt.mp (fun h2 => noAdj j h h2)) (hr (j+1)).1
            rcases (hnn (j+1)).lt_or_eq with hp | hp
            · left; rw [he, hl]; nlinarith [mul_pos hlL hp]
            · right; exact hp.symm
          · right; exact succ_zero hSM j h
      have hafter : ∀ k, m < k → π (k+1) = M.lamH * π k := by
        intro k hk
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
        rcases claim j (by omega) with h | h
        · exact le_antisymm (not_lt.mp (fun h2 => noAdj j h h2)) (hr (j+1)).1
        · have h1 := succ_zero hSM j h
          have h2 := succ_zero hSM (j+1) h1
          rw [h1, h2, mul_zero]
      refine ⟨m, ⟨hmin, hafter⟩, ?_⟩
      have hpm : 0 < π m := by
        by_contra hc; push Not at hc
        have h0 : π m = 0 := le_antisymm hc (hnn m)
        rw [h0, mul_zero] at hm; linarith [hnn (m+1)]
      have ha1 : (π (m+1) - M.lamH * π m) / (M.lamL * π m) < 1 := by
        rw [div_lt_one (mul_pos hlL hpm)]; rw [hl] at hm; linarith
      rcases lt_or_ge m N with hmN | hNm
      · have : (m:ℝ) + 1 ≤ N := by exact_mod_cast hmN
        linarith
      · have hupN : ∀ j, j < N → π (j+1) = M.lam * π j := fun j hj => hmin j (by omega)
        have hle : π (N+1) ≤ M.lamH * π N := not_lt.mp (noDown hupN)
        rcases hNm.lt_or_eq with hlt | heq
        · exfalso
          have hpN : 0 < π N := pos_of_le hSM hlt.le hpm
          have := hmin N hlt
          rw [hl] at this
          nlinarith [mul_pos hlL hpN]
        · subst heq
          have : π (N+1) - M.lamH * π N = 0 := le_antisymm (by linarith) (by linarith [(hr N).1])
          rw [this, zero_div, add_zero]
    · push Not at hex
      exfalso
      have hall : ∀ k, π (k+1) = M.lam * π k := fun k => le_antisymm (hr k).2 (hex k)
      have hposall : ∀ k, 0 < π k := by
        intro k
        induction k with
        | zero => exact h00
        | succ k ih => rw [hall k]; exact mul_pos (by rw [hl]; linarith) ih
      apply noDown (fun j _ => hall j)
      rw [hall N, hl]; nlinarith [mul_pos hlL (hposall N)]
  refine ⟨?_, hAt⟩
  obtain ⟨m, hm, -⟩ := hAt
  exact Or.inr ⟨m, hm⟩

end
end NPFBT2Aux

open NeedPersuasion.FirstBest in
theorem solution (M : Model) (hM : M.Standing) (π : ℕ → ℝ)
    (hπ : ParetoEfficientIn M (PiAP M) π) :
    HasThresholdStructure M π ∧ HasThresholdAtMost M π (mfi M) := by
  exact NPFBT2Aux.mainAP M hM π hπ
