-- Prove2me | solution 1 for NeedPersuasion.Homog.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T03:20:27.130562+00:00
-- url     : https://prove2.me/submissions/26d41c0c-6411-4d0d-b52a-85a310dbdfc5

import Mathlib
import Definitions.Def_NeedPersuasion_Homog_Model
import Definitions.Def_NeedPersuasion_Homog_BetaFi

set_option autoImplicit false

open Finset

namespace NPHAux
open NeedPersuasion.Homog

noncomputable def Dn (M : Model) (n : ℕ) : ℝ := ∑ k ∈ range (n+1), M.lamL ^ k
noncomputable def Nn (M : Model) (n : ℕ) : ℝ := ∑ k ∈ range n, M.lamL ^ (k+1) * M.uL k
noncomputable def T (M : Model) (n : ℕ) (k : ℕ) : ℝ := (if k ≤ n then M.lamL ^ k else 0) / Dn M n

noncomputable def cf (M : Model) (V μ : ℝ) : ℕ → ℝ
  | 0 => -V - μ * M.lamL * M.uL 0
  | (n+1) => (1+μ) * M.uL n - V - μ * M.lamL * M.uL (n+1)

lemma Dn_pos (M : Model) (hq : 0 < M.lamL) (n : ℕ) : 0 < Dn M n := by
  unfold Dn
  exact Finset.sum_pos (fun k _ => pow_pos hq k) ⟨0, by simp⟩

lemma Dn_succ (M : Model) (n : ℕ) : Dn M (n+1) = Dn M n + M.lamL ^ (n+1) := by
  unfold Dn; rw [Finset.sum_range_succ]

lemma Nn_succ (M : Model) (n : ℕ) : Nn M (n+1) = Nn M n + M.lamL ^ (n+1) * M.uL n := by
  unfold Nn; rw [Finset.sum_range_succ]

lemma tsum_w (M : Model) (n : ℕ) :
    (∑' j : ℕ, (if j ≤ n then M.lamL ^ j else 0 : ℝ)) = Dn M n := by
  rw [tsum_eq_sum (s := range (n+1))]
  · unfold Dn
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [show k ≤ n by omega]
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp [show ¬ k ≤ n by omega]

lemma tp_nat (M : Model) (hH : M.lamH = 0) (n : ℕ) :
    thresholdPolicy M (n : ℝ) = T M n := by
  have hw : (fun k : ℕ => if k ≤ ⌊(n:ℝ)⌋₊ then M.lam ^ k
      else M.lam ^ ⌊(n:ℝ)⌋₊ * (M.lamH + Int.fract (n:ℝ) * M.lamL) * M.lamH ^ (k - ⌊(n:ℝ)⌋₊ - 1))
      = fun k => if k ≤ n then M.lamL ^ k else 0 := by
    funext k
    simp [Nat.floor_natCast, Model.lam, hH]
  funext k
  show (fun k : ℕ => if k ≤ ⌊(n:ℝ)⌋₊ then M.lam ^ k
      else M.lam ^ ⌊(n:ℝ)⌋₊ * (M.lamH + Int.fract (n:ℝ) * M.lamL) * M.lamH ^ (k - ⌊(n:ℝ)⌋₊ - 1)) k /
      ∑' j, (fun k : ℕ => if k ≤ ⌊(n:ℝ)⌋₊ then M.lam ^ k
      else M.lam ^ ⌊(n:ℝ)⌋₊ * (M.lamH + Int.fract (n:ℝ) * M.lamL) * M.lamH ^ (k - ⌊(n:ℝ)⌋₊ - 1)) j = _
  rw [hw, tsum_w]
  rfl

lemma T_nonneg (M : Model) (hq : 0 < M.lamL) (n k : ℕ) : 0 ≤ T M n k := by
  unfold T
  apply div_nonneg _ (Dn_pos M hq n).le
  split_ifs
  · exact (pow_pos hq k).le
  · exact le_refl 0

lemma T_zero (M : Model) (n k : ℕ) (hk : n < k) : T M n k = 0 := by
  unfold T; simp [show ¬ k ≤ n by omega]

lemma T_le (M : Model) (n k : ℕ) (hk : k ≤ n) : T M n k = M.lamL ^ k / Dn M n := by
  unfold T; simp [hk]

lemma T_succ_eq (M : Model) (n k : ℕ) (hk : k < n) : T M n (k+1) = M.lamL * T M n k := by
  rw [T_le M n (k+1) (by omega), T_le M n k (by omega), pow_succ]; ring

lemma T_ratio (M : Model) (hq : 0 < M.lamL) (n k : ℕ) : T M n (k+1) ≤ M.lamL * T M n k := by
  rcases lt_or_ge k n with h | h
  · rw [T_succ_eq M n k h]
  · rw [T_zero M n (k+1) (by omega)]
    exact mul_nonneg hq.le (T_nonneg M hq n k)

lemma T_hasSum (M : Model) (hq : 0 < M.lamL) (n : ℕ) : HasSum (T M n) 1 := by
  have h : HasSum (T M n) (∑ k ∈ range (n+1), T M n k) := hasSum_sum_of_ne_finset_zero (by
    intro k hk
    simp only [Finset.mem_range] at hk
    exact T_zero M n k (by omega))
  convert h using 1
  rw [Finset.sum_congr rfl (fun k hk => T_le M n k (by simp at hk; omega)), ← Finset.sum_div]
  show (1:ℝ) = Dn M n / Dn M n
  rw [div_self (Dn_pos M hq n).ne']

lemma WL_eq (M : Model) (hH : M.lamH = 0) (π : ℕ → ℝ) :
    WL M π = ∑' n, π (n+1) * M.uL n := by
  unfold WL; simp [hH]

lemma leave_eq (M : Model) (hH : M.lamH = 0) (π : ℕ → ℝ) :
    leaveVal M π = ∑' n, (M.lamL * π n - π (n+1)) * M.uL n := by
  unfold leaveVal Model.lam; simp [hH]

lemma WL_fin (M : Model) (hH : M.lamH = 0) (π : ℕ → ℝ) (n : ℕ) (hs : ∀ k, n < k → π k = 0) :
    WL M π = ∑ k ∈ range n, π (k+1) * M.uL k := by
  rw [WL_eq M hH, tsum_eq_sum]
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [hs (k+1) (by omega)]; simp

lemma leave_fin (M : Model) (hH : M.lamH = 0) (π : ℕ → ℝ) (n : ℕ) (hs : ∀ k, n < k → π k = 0) :
    leaveVal M π = ∑ k ∈ range (n+1), (M.lamL * π k - π (k+1)) * M.uL k := by
  rw [leave_eq M hH, tsum_eq_sum]
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [hs k (by omega), hs (k+1) (by omega)]; simp

lemma WL_T (M : Model) (hH : M.lamH = 0) (n : ℕ) : WL M (T M n) = Nn M n / Dn M n := by
  rw [WL_fin M hH (T M n) n (fun k hk => T_zero M n k hk)]
  unfold Nn; rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [T_le M n (k+1) (by omega)]; ring

lemma abel (q : ℝ) (hq : 0 < q) (π c : ℕ → ℝ) (hπ0 : ∀ n, 0 ≤ π n)
    (hπq : ∀ n, π (n+1) ≤ q * π n)
    (hE : ∀ j, ∑ n ∈ range (j+1), q^n * c n ≤ 0) (K : ℕ) :
    ∑ n ∈ range (K+1), π n * c n ≤ 0 := by
  have key : ∀ K, q^K * ∑ n ∈ range (K+1), π n * c n ≤
      π K * ∑ n ∈ range (K+1), q^n * c n := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun n => q^n * c n)]
      have h1 : q * π K * (∑ n ∈ range (K+1), q^n * c n) ≤
          π (K+1) * ∑ n ∈ range (K+1), q^n * c n :=
        mul_le_mul_of_nonpos_right (hπq K) (hE K)
      have h2 : q^(K+1) * ∑ n ∈ range (K+1), π n * c n =
          q * (q^K * ∑ n ∈ range (K+1), π n * c n) := by ring
      have h5 := mul_le_mul_of_nonneg_left ih hq.le
      nlinarith
  have h0 := key K
  have h3 : π K * ∑ n ∈ range (K+1), q^n * c n ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hπ0 K) (hE K)
  have h4 : 0 < q^K := pow_pos hq K
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_pos h4 hcon]

lemma peak (q : ℝ) (hq : 0 < q) (c : ℕ → ℝ) (P : ℕ)
    (hEP : ∑ n ∈ range (P+1), q^n * c n ≤ 0)
    (hpos : ∀ n, 1 ≤ n → n ≤ P → 0 ≤ c n) (hneg : ∀ n, P < n → c n ≤ 0) :
    ∀ j, ∑ n ∈ range (j+1), q^n * c n ≤ 0 := by
  intro j
  rcases le_or_gt P j with hj | hj
  · induction j, hj using Nat.le_induction with
    | base => exact hEP
    | succ j hPj ih =>
      rw [Finset.sum_range_succ]
      have h1 := hneg (j+1) (by omega)
      have h2 := mul_nonpos_of_nonneg_of_nonpos (pow_pos hq (j+1)).le h1
      linarith
  · have key : ∀ d j, j + d = P →
        ∑ n ∈ range (j+1), q^n * c n ≤ ∑ n ∈ range (P+1), q^n * c n := by
      intro d
      induction d with
      | zero => intro j h; subst h; simp
      | succ d ih =>
        intro j h
        have h1 := ih (j+1) (by omega)
        rw [Finset.sum_range_succ (fun n => q^n * c n) (j+1)] at h1
        have h2 := hpos (j+1) (by omega) (by omega)
        have h3 := mul_nonneg (pow_pos hq (j+1)).le h2
        linarith
    exact (key (P - j) j (by omega)).trans hEP

lemma E_closed (M : Model) (V μ : ℝ) (j : ℕ) :
    ∑ n ∈ range (j+1), M.lamL^n * cf M V μ n =
      Nn M j - V * Dn M j - μ * M.lamL^(j+1) * M.uL j := by
  induction j with
  | zero => simp [Nn, Dn, cf]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, Nn_succ, Dn_succ]
    simp only [cf]
    ring

lemma UB (M : Model) (hq : 0 < M.lamL) (hH : M.lamH = 0) (V μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ K, m ≤ K → M.uL K < 0)
    (hE : ∀ j, ∑ n ∈ range (j+1), M.lamL^n * cf M V μ n ≤ 0)
    (π : ℕ → ℝ) (hπ : π ∈ PiSM M) : WL M π ≤ V := by
  obtain ⟨⟨h0, hsum, hrat, hsu, -⟩, -, hleave⟩ := hπ
  have hπq : ∀ n, π (n+1) ≤ M.lamL * π n := fun n => by
    have := (hrat n).2; simpa [Model.lam, hH] using this
  have hg : Summable (fun n => π (n+1) * M.uL n) := by
    refine Summable.of_norm_bounded (hsu.abs.mul_left M.lamL) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 (n+1))]
    have e : |π n * M.uL n| = π n * |M.uL n| := by rw [abs_mul, abs_of_nonneg (h0 n)]
    rw [e]
    have := mul_le_mul_of_nonneg_right (hπq n) (abs_nonneg (M.uL n))
    linarith
  have hWL : WL M π = ∑' n, π (n+1) * M.uL n := WL_eq M hH π
  have hL : leaveVal M π = M.lamL * ∑' n, π n * M.uL n - ∑' n, π (n+1) * M.uL n := by
    rw [leave_eq M hH, ← tsum_mul_left, ← (hsu.mul_left M.lamL).tsum_sub hg]
    congr 1; funext n; ring
  let P : ℕ → ℝ := fun K => (1+μ) * ∑ n ∈ range K, π (n+1) * M.uL n -
      ∑ n ∈ range K, (V * π n + μ * M.lamL * (π n * M.uL n))
  have hlim : Filter.Tendsto P Filter.atTop
      (nhds ((1+μ) * ∑' n, π (n+1) * M.uL n - (V * 1 + μ * M.lamL * ∑' n, π n * M.uL n))) := by
    have h1 := hg.hasSum.tendsto_sum_nat
    have h2 := hsum.tendsto_sum_nat
    have h3 := hsu.hasSum.tendsto_sum_nat
    have := (h1.const_mul (1+μ)).sub ((h2.const_mul V).add (h3.const_mul (μ * M.lamL)))
    refine this.congr (fun K => ?_)
    simp only [P, Finset.sum_add_distrib, Finset.mul_sum]
  have hPK : ∀ K, P (K+1) = ∑ n ∈ range (K+1), π n * cf M V μ n + (1+μ) * π (K+1) * M.uL K := by
    intro K
    induction K with
    | zero => simp [P, cf]; ring
    | succ K ih =>
      have e : P (K+2) = P (K+1) + ((1+μ) * (π (K+2) * M.uL (K+1)) -
          (V * π (K+1) + μ * M.lamL * (π (K+1) * M.uL (K+1)))) := by
        simp only [P, Finset.sum_range_succ]; ring
      rw [e, ih, Finset.sum_range_succ (fun n => π n * cf M V μ n) (K+1)]
      simp only [cf]
      ring
  have hev : ∀ K, m ≤ K → P (K+1) ≤ 0 := by
    intro K hK
    rw [hPK K]
    have a1 := abel M.lamL hq π (cf M V μ) h0 hπq hE K
    have a3 := hm K hK
    have a4 : 0 ≤ (1+μ) * π (K+1) := mul_nonneg (by linarith) (h0 _)
    have a2 := mul_nonpos_of_nonneg_of_nonpos a4 a3.le
    linarith
  have hlim0 : (1+μ) * ∑' n, π (n+1) * M.uL n -
      (V * 1 + μ * M.lamL * ∑' n, π n * M.uL n) ≤ 0 := by
    refine le_of_tendsto hlim ?_
    rw [Filter.eventually_atTop]
    refine ⟨m+1, fun K hK => ?_⟩
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    exact hev K' (by omega)
  rw [hL] at hleave
  rw [hWL]
  have := mul_nonneg hμ (show 0 ≤ -(M.lamL * ∑' n, π n * M.uL n - ∑' n, π (n+1) * M.uL n) by
    linarith)
  nlinarith

end NPHAux

namespace NPHAux
open NeedPersuasion.Homog

lemma lin_WL (M : Model) (hH : M.lamH = 0) (φ ψ : ℕ → ℝ) (n : ℕ) (a b : ℝ)
    (hφ : ∀ k, n < k → φ k = 0) (hψ : ∀ k, n < k → ψ k = 0) :
    WL M (fun k => a * φ k + b * ψ k) = a * WL M φ + b * WL M ψ := by
  rw [WL_fin M hH _ n (fun k hk => by simp [hφ k hk, hψ k hk]), WL_fin M hH φ n hφ,
    WL_fin M hH ψ n hψ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _; ring

lemma lin_leave (M : Model) (hH : M.lamH = 0) (φ ψ : ℕ → ℝ) (n : ℕ) (a b : ℝ)
    (hφ : ∀ k, n < k → φ k = 0) (hψ : ∀ k, n < k → ψ k = 0) :
    leaveVal M (fun k => a * φ k + b * ψ k) = a * leaveVal M φ + b * leaveVal M ψ := by
  rw [leave_fin M hH _ n (fun k hk => by simp [hφ k hk, hψ k hk]), leave_fin M hH φ n hφ,
    leave_fin M hH ψ n hψ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _; ring

set_option maxHeartbeats 1000000 in
lemma main (M : Model) (hM : M.Standing) (hH : M.lamH = 0) :
    (∀ π ∈ PiSM M, betaFi M * WL M π ≤ WL M (fi M)) ∧
      1 - 1 / ((mfi M : ℝ) + 1) ≤ betaFi M ∧
      ((∀ π ∈ PiSM M, WL M π ≤ WL M (fi M)) ↔
        WLx M ((mfi M : ℝ) - 1) ≤ WLx M (mfi M)) := by
  obtain ⟨hq, -, hlam, hu0, -, ⟨k0, hk0⟩, -, hanti, -, hconv⟩ := hM
  have hne : ({k | M.uL k < 0} : Set ℕ).Nonempty := ⟨k0, hk0⟩
  have hmneg : M.uL (mfi M) < 0 := Nat.sInf_mem hne
  have hmlt : ∀ k, k < mfi M → 0 ≤ M.uL k := fun k hk => by
    have := Nat.notMem_of_lt_sInf hk
    simp only [Set.mem_setOf_eq, not_lt] at this
    exact this
  have hm0 : mfi M ≠ 0 := by
    intro h; rw [h] at hmneg; linarith
  obtain ⟨p, hp⟩ : ∃ p, mfi M = p + 1 := ⟨mfi M - 1, by omega⟩
  have hq1 : M.lamL ≤ 1 := by
    have := hlam; simp only [Model.lam, hH, add_zero] at this; exact this
  have hneg : ∀ K, p + 1 ≤ K → M.uL K < 0 := fun K hK => by
    have := hanti.antitone hK; rw [hp] at hmneg; linarith
  have hnn : ∀ k, k ≤ p → 0 ≤ M.uL k := fun k hk => hmlt k (by omega)
  have hup : 0 ≤ M.uL p := hnn p le_rfl
  have hDp := Dn_pos M hq p
  have hDp1 := Dn_pos M hq (p+1)
  have ha : 0 < M.lamL ^ (p+1) := pow_pos hq _
  have hfi : fi M = T M (p+1) := by unfold fi; rw [hp]; exact tp_nat M hH (p+1)
  have hWLx1 : WLx M (mfi M) = WL M (T M (p+1)) := by unfold WLx; rw [hp, tp_nat M hH]
  have hWLx0 : WLx M ((mfi M : ℝ) - 1) = WL M (T M p) := by
    unfold WLx
    rw [show ((mfi M : ℝ) - 1) = (p : ℝ) by rw [hp]; push_cast; ring, tp_nat M hH]
  have hβ : betaFi M = Dn M p / Dn M (p+1) := by unfold betaFi Dn; rw [hp]
  have hWf : WL M (fi M) = Nn M (p+1) / Dn M (p+1) := by rw [hfi, WL_T M hH]
  have hNp1 : 0 ≤ Nn M (p+1) := by
    unfold Nn
    exact Finset.sum_nonneg (fun k hk => by
      simp only [Finset.mem_range] at hk
      exact mul_nonneg (pow_pos hq _).le (hnn k (by omega)))
  have hNs := Nn_succ M p
  have hDs := Dn_succ M p
  -- Case A bound
  have caseA : Nn M (p+1) / Dn M (p+1) ≤ M.uL p →
      ∀ π ∈ PiSM M, WL M π ≤ Nn M (p+1) / Dn M (p+1) := by
    intro hA π hπ
    have hV0 : 0 ≤ Nn M (p+1) / Dn M (p+1) := div_nonneg hNp1 hDp1.le
    refine UB M hq hH _ 0 le_rfl (p+1) hneg (peak M.lamL hq _ (p+1) ?_ ?_ ?_) π hπ
    · rw [E_closed]
      field_simp
      ring_nf
      exact le_refl _
    · intro n hn1 hnP
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [cf]
      have : M.uL p ≤ M.uL k := hanti.antitone (by omega)
      linarith
    · intro n hn
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [cf]
      have := hneg k (by omega)
      linarith
  -- Case B bound
  have caseB : M.uL p < Nn M (p+1) / Dn M (p+1) →
      ∀ π ∈ PiSM M, WL M π ≤ Nn M (p+1) / Dn M p := by
    intro hB π hπ
    set V := Nn M (p+1) / Dn M p with hV
    have hVge : Nn M (p+1) / Dn M (p+1) ≤ V := by
      rw [hV]
      apply div_le_div_of_nonneg_left hNp1 hDp
      rw [hDs]; linarith
    have hw : 0 < M.uL p - M.lamL * M.uL (p+1) := by
      have := hneg (p+1) (by omega)
      nlinarith
    set μ := (V - M.uL p) / (M.uL p - M.lamL * M.uL (p+1)) with hμ
    have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hw.le
    have hμw : μ * (M.uL p - M.lamL * M.uL (p+1)) = V - M.uL p := by
      rw [hμ]; field_simp
    have hcP : cf M V μ (p+1) = 0 := by
      simp only [cf]; nlinarith
    have hstep : ∀ k, cf M V μ (k+2) ≤ cf M V μ (k+1) := by
      intro k
      simp only [cf]
      have c1 : M.uL (k+1) - M.uL (k+1+1) ≤ M.uL k - M.uL (k+1) := hconv (by omega)
      have c2 : M.uL (k+2) < M.uL (k+1) := hanti (by omega)
      have c3 := mul_nonneg (mul_nonneg hμ0 (show 0 ≤ M.uL (k+1) - M.uL (k+2) by linarith))
        (show 0 ≤ 1 - M.lamL by linarith)
      have c4 := mul_nonneg hμ0 (show 0 ≤ (M.uL k - M.uL (k+1)) - (M.uL (k+1) - M.uL (k+2)) by
        simpa using c1)
      nlinarith
    have hanti' : Antitone (fun k => cf M V μ (k+1)) := antitone_nat_of_succ_le (fun k => hstep k)
    have hπV : WL M π ≤ V := by
      refine UB M hq hH V μ hμ0 (p+1) hneg (peak M.lamL hq _ p ?_ ?_ ?_) π hπ
      · rw [E_closed]
        have e1 : Nn M p - V * Dn M p = - M.lamL^(p+1) * M.uL p := by
          rw [hV, div_mul_cancel₀ _ hDp.ne', hNs]; ring
        rw [e1]
        have := mul_nonneg (mul_nonneg hμ0 ha.le) hup
        nlinarith [mul_nonneg ha.le hup]
      · intro n hn1 hnP
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have := hanti' (show k ≤ p by omega)
        simp only at this
        linarith
      · intro n hn
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have := hanti' (show p ≤ k by omega)
        simp only at this
        linarith
    exact hπV
  have hβ0 : 0 ≤ Dn M p / Dn M (p+1) := div_nonneg hDp.le hDp1.le
  have hβ1 : Dn M p / Dn M (p+1) ≤ 1 := by
    rw [div_le_one hDp1, hDs]; linarith
  have hWf0 : 0 ≤ Nn M (p+1) / Dn M (p+1) := div_nonneg hNp1 hDp1.le
  refine ⟨?_, ?_, ?_⟩
  · -- part 1
    intro π hπ
    rw [hβ, hWf]
    rcases le_or_gt (Nn M (p+1) / Dn M (p+1)) (M.uL p) with hA | hB
    · have h1 := caseA hA π hπ
      rcases le_total 0 (WL M π) with h2 | h2
      · nlinarith
      · nlinarith
    · have h1 := caseB hB π hπ
      have h2 := mul_le_mul_of_nonneg_left h1 hβ0
      calc Dn M p / Dn M (p+1) * WL M π ≤ Dn M p / Dn M (p+1) * (Nn M (p+1) / Dn M p) := h2
        _ = Nn M (p+1) / Dn M (p+1) := by field_simp
  · -- part 2
    rw [hβ, hp]
    push_cast
    have key : ((p:ℝ) + 1) * M.lamL ^ (p+1) ≤ Dn M p := by
      unfold Dn
      have := Finset.sum_le_sum (s := range (p+1)) (f := fun _ => M.lamL ^ (p+1))
        (g := fun k => M.lamL ^ k) (fun k hk => by
          simp only [Finset.mem_range] at hk
          exact pow_le_pow_of_le_one hq.le hq1 (by omega))
      simpa using this
    rw [le_div_iff₀ hDp1, hDs]
    have e : (1:ℝ) - 1 / ((p:ℝ) + 1 + 1) = ((p:ℝ) + 1) / ((p:ℝ) + 2) := by
      field_simp; ring
    rw [e, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  · -- part 3
    rw [hWLx0, hWLx1, WL_T M hH, WL_T M hH]
    constructor
    · intro h
      by_contra hlt
      push_neg at hlt
      -- mixture
      have hsg : ∀ k, p + 1 < k → T M p k = 0 := fun k hk => T_zero M p k (by omega)
      have hsf : ∀ k, p + 1 < k → T M (p+1) k = 0 := fun k hk => T_zero M (p+1) k hk
      have hLg : 0 ≤ leaveVal M (T M p) := by
        rw [leave_fin M hH _ p (fun k hk => T_zero M p k hk)]
        exact Finset.sum_nonneg (fun k hk => by
          simp only [Finset.mem_range] at hk
          exact mul_nonneg (by linarith [T_ratio M hq p k]) (hnn k (by omega)))
      have hLf : leaveVal M (T M (p+1)) < 0 := by
        rw [leave_fin M hH _ (p+1) (fun k hk => T_zero M (p+1) k hk), Finset.sum_range_succ,
          Finset.sum_eq_zero (fun k hk => by
            simp only [Finset.mem_range] at hk
            rw [T_succ_eq M (p+1) k (by omega)]; ring),
          T_zero M (p+1) (p+1+1) (by omega), T_le M (p+1) (p+1) le_rfl]
        have := hneg (p+1) le_rfl
        have : 0 < M.lamL * (M.lamL ^ (p+1) / Dn M (p+1)) := mul_pos hq (div_pos ha hDp1)
        nlinarith
      obtain ⟨Lg, hLgd⟩ : ∃ x, x = leaveVal M (T M p) := ⟨_, rfl⟩
      obtain ⟨Lf, hLfd⟩ : ∃ x, x = leaveVal M (T M (p+1)) := ⟨_, rfl⟩
      rw [← hLgd] at hLg
      rw [← hLfd] at hLf
      have hden : 0 < Lg - Lf := by linarith
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Lg / (Lg - Lf) := ⟨_, rfl⟩
      have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hLg hden.le
      have ht1 : 1 - t = -Lf / (Lg - Lf) := by rw [ht]; field_simp; ring
      have ht1p : 0 < 1 - t := by rw [ht1]; exact div_pos (by linarith) hden
      obtain ⟨π, hπdef⟩ : ∃ π : ℕ → ℝ, π = fun k => (1 - t) * T M p k + t * T M (p+1) k :=
        ⟨_, rfl⟩
      have hsπ : ∀ k, p + 1 < k → π k = 0 := fun k hk => by
        rw [hπdef]; simp only [hsg k hk, hsf k hk]; ring
      have hWLπ : WL M π = (1 - t) * WL M (T M p) + t * WL M (T M (p+1)) := by
        rw [hπdef]; exact lin_WL M hH _ _ (p+1) _ _ hsg hsf
      have hLπ : leaveVal M π = (1 - t) * Lg + t * Lf := by
        rw [hπdef, hLgd, hLfd]; exact lin_leave M hH _ _ (p+1) _ _ hsg hsf
      have hLπ0 : leaveVal M π = 0 := by
        rw [hLπ, ht1, ht]; field_simp; ring
      rw [WL_T M hH, WL_T M hH] at hWLπ
      have hgt : Nn M (p+1) / Dn M (p+1) < WL M π := by
        rw [hWLπ]
        have := mul_pos ht1p (sub_pos.2 hlt)
        linarith
      have hmem : π ∈ PiSM M := by
        refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
        · intro k
          rw [hπdef]
          exact add_nonneg (mul_nonneg ht1p.le (T_nonneg M hq p k))
            (mul_nonneg ht0 (T_nonneg M hq (p+1) k))
        · have := ((T_hasSum M hq p).mul_left (1 - t)).add ((T_hasSum M hq (p+1)).mul_left t)
          rw [hπdef]
          have e : (1 - t) * 1 + t * 1 = (1:ℝ) := by ring
          rw [e] at this
          exact this
        · intro k
          rw [hπdef]
          simp only [Model.lam, hH, zero_mul, add_zero]
          constructor
          · exact add_nonneg (mul_nonneg ht1p.le (T_nonneg M hq p (k+1)))
              (mul_nonneg ht0 (T_nonneg M hq (p+1) (k+1)))
          · have e1 := mul_le_mul_of_nonneg_left (T_ratio M hq p k) ht1p.le
            have e2 := mul_le_mul_of_nonneg_left (T_ratio M hq (p+1) k) ht0
            linarith
        · exact summable_of_ne_finset_zero (s := range (p+2)) (fun k hk => by
            simp only [Finset.mem_range, not_lt] at hk
            rw [hsπ k (by omega)]; ring)
        · exact summable_of_ne_finset_zero (s := range (p+2)) (fun k hk => by
            simp only [Finset.mem_range, not_lt] at hk
            rw [hsπ k (by omega)]; ring)
        · show 0 ≤ WL M π
          linarith
        · rw [hLπ0]
      have h2 := h π hmem
      rw [hWf] at h2
      linarith
    · intro hle π hπ
      rw [hWf]
      apply caseA _ π hπ
      rw [hNs, hDs] at hle ⊢
      rw [div_le_div_iff₀ hDp (by linarith)] at hle
      rw [div_le_iff₀ (by linarith)]
      by_contra hc
      push_neg at hc
      have e1 : M.uL p * (Dn M p + M.lamL ^ (p+1)) = M.uL p * Dn M p + M.lamL ^ (p+1) * M.uL p := by
        ring
      have hlt2 : M.uL p * Dn M p < Nn M p := by linarith
      have h3 := mul_pos ha (sub_pos.2 hlt2)
      have e3 : Nn M p * (Dn M p + M.lamL ^ (p+1)) = Nn M p * Dn M p + M.lamL ^ (p+1) * Nn M p := by
        ring
      have e4 : (Nn M p + M.lamL ^ (p+1) * M.uL p) * Dn M p =
          Nn M p * Dn M p + M.lamL ^ (p+1) * (M.uL p * Dn M p) := by ring
      have e5 : M.lamL ^ (p+1) * (Nn M p - M.uL p * Dn M p) =
          M.lamL ^ (p+1) * Nn M p - M.lamL ^ (p+1) * (M.uL p * Dn M p) := by ring
      linarith

end NPHAux

open NeedPersuasion.Homog in
theorem solution (M : Model) (hM : M.Standing) (hH : M.lamH = 0) :
    (∀ π ∈ PiSM M, betaFi M * WL M π ≤ WL M (fi M)) ∧
      1 - 1 / ((mfi M : ℝ) + 1) ≤ betaFi M ∧
      ((∀ π ∈ PiSM M, WL M π ≤ WL M (fi M)) ↔
        WLx M ((mfi M : ℝ) - 1) ≤ WLx M (mfi M)) := by
  exact NPHAux.main M hM hH
