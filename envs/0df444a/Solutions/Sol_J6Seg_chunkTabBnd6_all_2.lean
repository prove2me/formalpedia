-- Prove2me | solution 2 for J6Seg.chunkTabBnd6_all
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:58:08.961932+00:00
-- url     : https://prove2.me/submissions/1ad374f9-474b-4e35-84b7-ce3500c0bbb2

import Definitions.Def_IntMul_Kappa_R6_Defs70
import Theorems.Thm_J6Seg_r6_axis_nat
import Theorems.Thm_J6Seg_fit_PE
import Theorems.Thm_J6Seg_fit_ddle
import Theorems.Thm_J6Seg_TabBnd_tab_bnd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open IntMul NLogN IntMul.Kappa.R6 Function
open IntMul.HvdH IntMul.HvdH.P47 IntMul.HvdH.JPf
open J6Seg J6Seg.TabBnd

private theorem lg_ge (B : ℕ) {n : ℕ} (hn : 2 ^ B ≤ n) : B ≤ bP6 n := by
  have h := Nat.clog_mono_right 2 hn
  rw [Nat.clog_pow 2 B (by norm_num)] at h
  exact h.trans (le_max_left _ _)

private theorem eventually_b_ge (B : ℕ) : ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → B ≤ bP6 n :=
  ⟨2 ^ B, fun _ hn => lg_ge B hn⟩

private theorem eventually_d_ge (P : Prm) (hP : P.Ok) (D₀ : ℕ) :
    ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → D₀ ≤ dP6 P n := by
  obtain ⟨n₁, hn₁⟩ := eventually_b_ge (4 + 4 * D₀ ^ 2)
  refine ⟨n₁, fun n hn => ?_⟩
  have hb := hn₁ n hn
  have hb4 : 4 ≤ bP6 n := by omega
  have h1 := d_half P hP hb4
  have hB : ((4 + 4 * D₀ ^ 2 : ℕ) : ℝ) ≤ bP6 n := by exact_mod_cast hb
  have hB1 : (1 : ℝ) ≤ bP6 n := by push_cast at hB; nlinarith
  have h2 : (bP6 n : ℝ) ^ ((1 : ℝ) / 2) ≤ (bP6 n : ℝ) ^ P.ε :=
    Real.rpow_le_rpow_of_exponent_le hB1 hP.eps_ge
  have h3 : ((bP6 n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = bP6 n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have h4 : (2 * D₀ : ℝ) ≤ (bP6 n : ℝ) ^ ((1 : ℝ) / 2) := by
    have h0 : (0 : ℝ) ≤ (bP6 n : ℝ) ^ ((1 : ℝ) / 2) := by positivity
    push_cast at hB
    nlinarith
  have : (D₀ : ℝ) ≤ dP6 P n := by linarith
  exact_mod_cast this

private theorem r6_axis_hyps (P : Prm) (hP : P.Ok) : ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → ∀ src : ℕ → ℕ,
    SrcOK6 P n src → ∀ j < dP6 P n,
      0 < src j ∧ src j < tF6 P n j ∧ 2 ≤ αN6 P n ∧
      3 ≤ IntMul.HvdH.JPf.xθ (src j) (tF6 P n j) (αN6 P n) := by
  obtain ⟨n₁, h⟩ := r6_axis_nat P hP
  refine ⟨n₁, fun n hn src hsrc j hj => ?_⟩
  obtain ⟨hs0, hst, hα2, hkey, -⟩ := h n hn src hsrc j hj
  refine ⟨hs0, hst, hα2, ?_⟩
  unfold IntMul.HvdH.JPf.xθ
  have hsR : (0 : ℝ) < src j := by exact_mod_cast hs0
  rw [le_div_iff₀ hsR]
  exact_mod_cast hkey

private theorem r6_axis_fit (P : Prm) (hP : P.Ok) : ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → ∀ src : ℕ → ℕ,
    SrcOK6 P n src → ∀ j < dP6 P n,
      3 * dP6 P n ^ 2 * (tF6 P n j - src j) ≤ src j ∧ 6 * dP6 P n ^ 2 ≤ src j ∧
      48 * dP6 P n * αN6 P n ^ 2 ≤ pP6 P n ∧ 2 ≤ dP6 P n := by
  obtain ⟨n₁, hn₁⟩ := eventually_d_ge P hP 2
  refine ⟨n₁, fun n hn src hsrc j hj => ?_⟩
  have hd2 := hn₁ n hn
  set d := dP6 P n
  have hlo := hsrc.lo j hj
  have hhi := hsrc.hi j hj
  set t := tF6 P n j
  set w := wnd6 P n j
  have hwdef : w = t / (8 * d ^ 2) := rfl
  have hw1 : 1 ≤ w := by omega
  have hwt : 8 * d ^ 2 * w ≤ t := by rw [hwdef]; exact Nat.mul_div_le t _
  have hd2' : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e : 8 * d ^ 2 * w = 8 * (d ^ 2 * w) := by ring
  have h1 : d ^ 2 * 1 ≤ d ^ 2 * w := Nat.mul_le_mul_left _ hw1
  have h2 : 1 * w ≤ d ^ 2 * w := Nat.mul_le_mul_right w hd2'
  have hts : t - src j ≤ 2 * w := by omega
  have h3 : 3 * d ^ 2 * (t - src j) ≤ 3 * d ^ 2 * (2 * w) := Nat.mul_le_mul_left _ hts
  have e3 : 3 * d ^ 2 * (2 * w) = 6 * (d ^ 2 * w) := by ring
  have hsX : 6 * (d ^ 2 * w) ≤ src j := by
    rw [e] at hwt
    generalize d ^ 2 * w = X at hwt h1 h2
    omega
  refine ⟨by omega, by omega, ?_, hd2⟩
  have ha : αN6 P n ^ 2 ≤ α2P6 P n := Nat.sqrt_le' _
  have hb : 48 * d * α2P6 P n ≤ 6 * b'P6 P n := by
    have := Nat.div_mul_le_self (6 * b'P6 P n) (48 * d)
    have e2 : α2P6 P n = 6 * b'P6 P n / (48 * d) := rfl
    rw [e2]; linarith
  have e4 : pP6 P n = 6 * b'P6 P n := rfl
  have : 48 * d * αN6 P n ^ 2 ≤ 48 * d * α2P6 P n := Nat.mul_le_mul_left _ ha
  omega

private theorem tF6_coprime (P : Prm) (n j s : ℕ) (hs : Odd s) : Nat.Coprime s (tF6 P n j) := by
  have h2 : Nat.Coprime s 2 := Nat.coprime_two_right.2 hs
  unfold tF6; split_ifs
  · rw [← pow_succ]; exact Nat.Coprime.pow_right _ h2
  · exact Nat.Coprime.pow_right _ h2

private theorem lamP_le (d : ℕ) (hd : 1 ≤ d) : lamP d ≤ lamF d := by
  unfold lamP
  have : 1 ≤ lamF d := by unfold lamF kF; nlinarith
  exact Nat.pow_log_le_self 2 (by omega)

private theorem lamP_pos (d : ℕ) : 1 ≤ lamP d := Nat.one_le_two_pow

private theorem kF_sq (d : ℕ) (hd : 1 ≤ d) : d < kF d ^ 2 ∧ kF d ^ 2 ≤ 4 * d := by
  have h1 := Nat.lt_succ_sqrt d
  have h2 : 1 ≤ Nat.sqrt d := Nat.le_sqrt.2 (by omega)
  have h3 := Nat.sqrt_le' d
  unfold kF; constructor <;> nlinarith

private theorem r6_segReg (P : Prm) (hP : P.Ok) : ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → ∀ src : ℕ → ℕ,
    SrcOK6 P n src → ∀ j < dP6 P n,
      SegReg (segPF (pP6 P n) (dP6 P n) (src j)) (pP6 P n / 7) (src j) (tF6 P n j)
        (lamP (dP6 P n)) (wF (dP6 P n)) (αN6 P n) := by
  obtain ⟨n₁, h⟩ := r6_axis_nat P hP
  obtain ⟨n₂, h'⟩ := r6_axis_fit P hP
  obtain ⟨n₃, h''⟩ := r6_axis_hyps P hP
  refine ⟨max n₁ (max n₂ n₃), fun n hn src hsrc j hj => ?_⟩
  have hn1 : n₁ ≤ n := by omega
  have hn2 : n₂ ≤ n := by omega
  have hn3 : n₃ ≤ n := by omega
  obtain ⟨hs0, hst, hα2, hkey, -, hαd, hαp, hpα, hb', hd1⟩ := h n hn1 src hsrc j hj
  obtain ⟨hθ, h6d, h48d, hd2⟩ := h' n hn2 src hsrc j hj
  obtain ⟨-, -, -, hx⟩ := h'' n hn3 src hsrc j hj
  have h48 : 48 ≤ αN6 P n ^ 2 := by
    have : 48 * 1 ≤ 48 * dP6 P n ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hd1)
    omega
  have hp : 100 ≤ pP6 P n := by have e : pP6 P n = 6 * b'P6 P n := rfl; omega
  have : NeZero (src j) := ⟨by omega⟩
  have : NeZero (tF6 P n j) := ⟨by omega⟩
  have hcop := tF6_coprime P n j (src j) (hsrc.odd j hj)
  have hl1 := lamP_pos (dP6 P n)
  have hlF := lamP_le (dP6 P n) hd1
  have hDle := fit_ddle (pP6 P n) (dP6 P n) (src j) (tF6 P n j) (αN6 P n) (lamP (dP6 P n)) hst
    hcop hα2 hαp hkey hd2 h6d h48 hpα hθ h48d hp hl1 hlF
  obtain ⟨hPE, -, -⟩ := fit_PE (pP6 P n) (dP6 P n) (src j) (tF6 P n j) (αN6 P n)
    (lamP (dP6 P n)) hst hcop hα2 hαp hkey hd2 h6d h48 hpα hθ h48d hp hl1 hlF hDle
  obtain ⟨hk1, hk2⟩ := kF_sq (dP6 P n) (by omega)
  have hws : wF (dP6 P n) ≤ src j := by
    unfold wF
    have hks : kF (dP6 P n) ≤ dP6 P n + 1 := by
      unfold kF; exact Nat.add_le_add_right (Nat.sqrt_le_self _) 1
    have h7 : 7 * (dP6 P n + 1) ≤ 6 * dP6 P n ^ 2 := by nlinarith
    have : 7 * kF (dP6 P n) ≤ 6 * dP6 P n ^ 2 :=
      (Nat.mul_le_mul_left 7 hks).trans h7
    exact this.trans h6d
  exact ⟨hs0, hst.le, hα2, hx, hl1, hws, hDle, hPE⟩

private theorem NF_lt_Q (p d s : ℕ) : NF d s < 2 ^ segPF p d s := by
  have h := Nat.lt_size_self (NF d s)
  exact h.trans_le (Nat.pow_le_pow_right (by norm_num) (by unfold segPF; omega))

private theorem lam_P_le (p d s : ℕ) : 200 * (3 * lamP d + 1) < 2 ^ segPF p d s := by
  have hl : lamP d ≤ lamF d + 1 := by
    unfold lamP
    by_cases h0 : lamF d = 0
    · rw [h0]; simp
    · have := Nat.pow_log_le_self 2 h0; omega
  have hN : 1500 * ((lamF d + 1) * (3 * lamF d + 3) + 1) ≤ NF d s := by
    unfold NF
    have a1 : 0 < lamF d + 1 := by omega
    have a2 : 0 < 2 * wF d + 1 := by omega
    have a3 : 0 < (s + 1) ^ 2 := by positivity
    calc 1500 * ((lamF d + 1) * (3 * lamF d + 3) + 1)
        ≤ 1500 * ((lamF d + 1) * (3 * lamF d + 3) + 1) * (lamF d + 1) :=
          Nat.le_mul_of_pos_right _ a1
      _ ≤ 1500 * ((lamF d + 1) * (3 * lamF d + 3) + 1) * (lamF d + 1) * (2 * wF d + 1) :=
          Nat.le_mul_of_pos_right _ a2
      _ ≤ _ := Nat.le_mul_of_pos_right _ a3
  have h3 : 3 * lamF d + 3 ≤ (lamF d + 1) * (3 * lamF d + 3) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have := NF_lt_Q p d s
  omega

theorem solution (P : IntMul.Kappa.R6.Prm) (hP : P.Ok) : J6Seg.ChunkTabBnd6 P := by
  obtain ⟨n₁, hR⟩ := r6_segReg P hP
  refine ⟨n₁, fun n hn src hsrc D hD k hk => ?_⟩
  have h := hR n hn src hsrc k (by omega)
  have hQ1 : 1 ≤ J6Seg.Q6 (pP6 P n) (dP6 P n) (src k) := by unfold J6Seg.Q6 segPF; omega
  have hPl : 200 * (3 * (lamP (dP6 P n) : ℝ) + 1) ≤
      2 ^ J6Seg.Q6 (pP6 P n) (dP6 P n) (src k) := by
    have := lam_P_le (pP6 P n) (dP6 P n) (src k)
    have h' : ((200 * (3 * lamP (dP6 P n) + 1) : ℕ) : ℝ) ≤
        ((2 ^ segPF (pP6 P n) (dP6 P n) (src k) : ℕ) : ℝ) := by exact_mod_cast this.le
    push_cast at h'; exact h'
  exact tab_bnd h.hs h.hst h.hα hQ1 h.hl hPl h.hR

end
