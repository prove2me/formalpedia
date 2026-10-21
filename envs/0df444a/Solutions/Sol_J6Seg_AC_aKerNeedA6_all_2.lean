-- Prove2me | solution 2 for J6Seg.AC.aKerNeedA6_all
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:41:04.838572+00:00
-- url     : https://prove2.me/submissions/2435c5d5-dfcc-44ae-813e-78321fd86efb

import Definitions.Def_IntMul_Kappa_R6_Defs70
import Theorems.Thm_J6Seg_Side_axNum_ev
import Theorems.Thm_J6Seg_axA_geom
import Theorems.Thm_J6Seg_AC_aSide_at
import Theorems.Thm_J6Seg_AC_akCond_at
import Theorems.Thm_J6Seg_AC_kerA_le

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open IntMul NLogN IntMul.Kappa.R6 J6Seg J6Seg.Side J6Seg.KR J6Seg.KR.AK J6Seg.Ax J6Seg.AC
open IntMul.HvdH

/-! Private helpers transplanted from the round-six solution. -/

private theorem lg_ge (B : ℕ) {n : ℕ} (hn : 2 ^ B ≤ n) : B ≤ bP6 n := by
  have h := Nat.clog_mono_right 2 hn
  rw [Nat.clog_pow 2 B (by norm_num)] at h
  exact h.trans (le_max_left _ _)

private theorem lgn_ge (n : ℕ) : 1 ≤ Real.log (IntMul.lg n) + 1 := by
  have : (1 : ℝ) ≤ IntMul.lg n := by exact_mod_cast bP6_pos n
  have := Real.log_nonneg this; linarith

private theorem dl_le_Ncost6 (P : Prm) (n : ℕ) : (dP6 P n : ℝ) + ℓP6 P n ≤ Ncost6 P n := by
  unfold Ncost6 Ncost6R
  have hp1 : (1 : ℝ) ≤ pP6 P n := by
    have := b'P6_pos P n
    have : 1 ≤ pP6 P n := by unfold pP6; omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) ≤ pP6 P n := by linarith
  have hd : (0 : ℝ) ≤ dP6 P n := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ ℓP6 P n := Nat.cast_nonneg _
  have t1 : 0 ≤ (ℓP6 P n : ℝ) * (dP6 P n : ℝ) ^ P.lamp := mul_nonneg hl (Real.rpow_nonneg hd _)
  have t2 : 0 ≤ (dP6 P n : ℝ) * (pP6 P n : ℝ) ^ P.δ := mul_nonneg hd (Real.rpow_nonneg hp0 _)
  have t3 : 0 ≤ Real.logb 2 (pP6 P n) := Real.logb_nonneg (by norm_num) hp1
  have t4 : 0 ≤ (pP6 P n : ℝ) ^ P.δ := Real.rpow_nonneg hp0 _
  have t5 : 0 ≤ (ℓP6 P n : ℝ) * ((dP6 P n : ℝ) * Real.log (pP6 P n)) ^ P.τ :=
    mul_nonneg hl (Real.rpow_nonneg (mul_nonneg hd (Real.log_nonneg hp1)) _)
  linarith

private theorem beta_le (n : ℕ) :
    ((Nat.log 2 (bP6 n) : ℕ) : ℝ) + 1 ≤ 2 * (Real.log (IntMul.lg n) + 1) := by
  have hb := bP6_pos n
  have h1 : 2 ^ Nat.log 2 (bP6 n) ≤ bP6 n := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 (bP6 n) ≤ (IntMul.lg n : ℝ) := by
    show ((2 : ℝ)) ^ Nat.log 2 (bP6 n) ≤ (bP6 n : ℝ); exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have hl2 := Real.log_two_gt_d9
  have hβ : (0 : ℝ) ≤ (Nat.log 2 (bP6 n) : ℝ) := Nat.cast_nonneg _
  nlinarith

private theorem fin {Y M Kc Z d : ℝ} (hd : 0 < d) (hZ : 0 ≤ Z) (hM : M ≤ Kc) (hY : d * Y ≤ M * Z) :
    Y ≤ Kc * Z / d := by
  rw [le_div_iff₀ hd]
  calc Y * d = d * Y := by ring
    _ ≤ M * Z := hY
    _ ≤ Kc * Z := mul_le_mul_of_nonneg_right hM hZ

private theorem lift {Y M X Nc L d : ℝ} (hd : 0 ≤ d) (hdN : d ≤ Nc) (hX : 0 ≤ X) (hM : 0 ≤ M)
    (hY : Y ≤ M * X * L ^ 2) : d * Y ≤ M * (X * Nc * L ^ 2) := by
  have h0 : 0 ≤ M * X * L ^ 2 := by positivity
  calc d * Y ≤ d * (M * X * L ^ 2) := mul_le_mul_of_nonneg_left hY hd
    _ ≤ Nc * (M * X * L ^ 2) := mul_le_mul_of_nonneg_right hdN h0
    _ = M * (X * Nc * L ^ 2) := by ring

private theorem sW_le (p d : ℕ) (hd : 1 ≤ d) (hp : 1 ≤ p) :
    IntMul.HvdH.sWidth p (Nat.sqrt (p / (48 * d))) ≤ p := by
  unfold IntMul.HvdH.sWidth IntMul.HvdH.ceilSqrt
  set s := Nat.sqrt p with hsd
  have hs : s * s ≤ p := Nat.sqrt_le p
  have hs1 : 1 ≤ s := Nat.sqrt_pos.2 hp
  set a := Nat.sqrt (p / (48 * d)) with had
  have ha : a * a ≤ p / (48 * d) := Nat.sqrt_le _
  have ha2 : a * a * 48 ≤ p := by
    have h1 := Nat.div_mul_le_self p (48 * d)
    have h2 : a * a * 48 ≤ a * a * (48 * d) := Nat.mul_le_mul_left _ (by omega)
    have h3 : a * a * (48 * d) ≤ p / (48 * d) * (48 * d) := Nat.mul_le_mul_right _ ha
    omega
  have hc : (if s * s < p then s + 1 else s) ≤ s + 1 := by split_ifs <;> omega
  set c := (if s * s < p then s + 1 else s)
  have hcc : c * c ≤ 4 * p := by
    have : c * c ≤ (s + 1) * (s + 1) := Nat.mul_le_mul hc hc
    nlinarith
  have key : (c * a) * (c * a) ≤ p * p := by
    have e : (c * a) * (c * a) = (c * c) * (a * a) := by ring
    rw [e]
    have : (c * c) * (a * a) * 48 ≤ (4 * p) * p := by
      calc (c * c) * (a * a) * 48 = (c * c) * (a * a * 48) := by ring
        _ ≤ (4 * p) * p := Nat.mul_le_mul hcc ha2
    nlinarith
  exact Nat.mul_self_le_mul_self_iff.1 key

private theorem m_le (P : Prm) (n : ℕ) (hd : 1 ≤ dP6 P n) (hp : 1 ≤ pP6 P n) :
    IntMul.HvdH.sWidth (pP6 P n) (αN6 P n) ≤ pP6 P n := sW_le _ _ hd hp

private theorem HA_le (P : Prm) (n : ℕ) (hd : 1 ≤ dP6 P n) (hp : 1 ≤ pP6 P n) :
    HA6 P n ≤ pP6 P n := by
  unfold HA6
  have hm := m_le P n hd hp
  by_cases h0 : IntMul.HvdH.sWidth (pP6 P n) (αN6 P n) = 0
  · rw [h0]; simpa using hp
  · exact (Nat.pow_log_le_self 2 h0).trans hm

private theorem flog_le (P : Prm) (n : ℕ) (hd : 1 ≤ dP6 P n) (hp : 1 ≤ pP6 P n)
    (hb : bP6 n < 2 ^ (Nat.log 2 (bP6 n) + 1)) :
    Nat.log 2 (IntMul.HvdH.sWidth (pP6 P n) (αN6 P n)) + 3 + 1 ≤
      (P.x + 8) * (Nat.log 2 (bP6 n) + 1) := by
  have hm := m_le P n hd hp
  have h1 : Nat.log 2 (IntMul.HvdH.sWidth (pP6 P n) (αN6 P n)) ≤ Nat.log 2 (pP6 P n) :=
    Nat.log_mono_right hm
  set β := Nat.log 2 (bP6 n)
  have hpw : pP6 P n < 2 ^ (3 + (1 + P.x) * (β + 1)) := by
    have e1 : pP6 P n = 6 * bP6 n ^ (1 + P.x) := rfl
    have e2 : bP6 n ^ (1 + P.x) < (2 ^ (β + 1)) ^ (1 + P.x) :=
      Nat.pow_lt_pow_left hb (by omega)
    rw [← pow_mul, Nat.mul_comm] at e2
    rw [pow_add, e1]
    have : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  have h2 : Nat.log 2 (pP6 P n) < 3 + (1 + P.x) * (β + 1) :=
    Nat.log_lt_of_lt_pow (by omega) hpw
  nlinarith

private theorem axANum_ev (P : Prm) (hP : P.Ok) : ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → ∀ src : ℕ → ℕ,
    SrcOK6 P n src → ∀ D : ℕ, dP6 P n = D + 1 → ∀ k ≤ D, AxANum P n src D k := by
  obtain ⟨n₁, hN⟩ := axNum_ev P hP
  obtain ⟨n₂, hG⟩ := axA_geom P hP
  refine ⟨max n₁ n₂, fun n hn src hsrc D hD k hk => ?_⟩
  have h := hN n (le_of_max_le_left hn) src hsrc D hD k hk
  obtain ⟨hH, hM0, ht, hWs, hst, hsep, hWw, hf, -, -⟩ :=
    hG n (le_of_max_le_right hn) src hsrc D hD k hk
  exact ⟨h, hH, hM0, ht, hWs, hst, hsep, hWw, hf, HA_le P n h.d1 h.p1,
    flog_le P n h.d1 h.p1 h.bβ⟩

private theorem KAs_nonneg (P : Prm) : 0 ≤ KAs P := by unfold KAs; positivity

private theorem KKA_nonneg (P : Prm) : 0 ≤ KKA P := by unfold KKA; positivity

private theorem tabsT_len (f : ℕ → List ℤ) (L : ℕ) (hf : ∀ q, (f q).length = L) :
    ∀ N, (tabsT f N).length = N * (L + 1)
  | 0 => by simp [tabsT]
  | N + 1 => by
    have ih := tabsT_len f L hf N
    simp only [tabsT, List.range_succ, List.flatMap_append, List.length_append] at ih ⊢
    rw [ih]; simp [segT, hf]; ring

private theorem aTabG_length (p s t α H pk b q : ℕ) :
    (aTabG p s t α H pk b q).length =
      17 + 2 * J6A.WA p α H + (2 * J6A.WA p α H + 2 * H) + 2 * H := by
  simp only [aTabG, aKTab2, aHdr2, List.length_append, List.length_cons, List.length_nil,
    J6A.aTabA, J6A.rTabA, J6A.cTabA, List.length_map, List.length_range]
  ring

private theorem toU2 (P : Prm) {n D : ℕ} (hD : dP6 P n = D + 1) {Y c : ℕ}
    (hY : Y ≤ c * (TP6 P n * pP6 P n * (Nat.log 2 (bP6 n) + 1) ^ 2)) {KK : ℝ}
    (hc : 4 * (c : ℝ) ≤ KK) : (Y : ℝ) ≤ KK * (cU6 P n 2 / (D + 1)) := by
  have hdR : ((D : ℝ) + 1) = (dP6 P n : ℝ) := by rw [hD]; push_cast; ring
  have hcU : cU6 P n 2 = ((TP6 P n : ℝ) * pP6 P n) * Ncost6 P n *
      (Real.log (IntMul.lg n) + 1) ^ 2 := rfl
  rw [hdR, hcU, ← mul_div_assoc]
  have hd0 : (0 : ℝ) < dP6 P n := by
    have : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    linarith
  have hdl := dl_le_Ncost6 P n
  have hℓ0 : (0 : ℝ) ≤ ℓP6 P n := Nat.cast_nonneg _
  have hdN : (dP6 P n : ℝ) ≤ Ncost6 P n := by linarith
  have hL := lgn_ge n
  have hβ := beta_le n
  set L := Real.log (IntMul.lg n) + 1
  have hY' : (Y : ℝ) ≤ c * ((TP6 P n : ℝ) * pP6 P n * (((Nat.log 2 (bP6 n) : ℕ) : ℝ) + 1) ^ 2) := by
    exact_mod_cast hY
  have hTp : (0 : ℝ) ≤ (TP6 P n : ℝ) * pP6 P n := by positivity
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have h2 : (Y : ℝ) ≤ (4 * c) * ((TP6 P n : ℝ) * pP6 P n) * L ^ 2 := by
    have hb0 : (0 : ℝ) ≤ ((Nat.log 2 (bP6 n) : ℕ) : ℝ) + 1 := by positivity
    have : (((Nat.log 2 (bP6 n) : ℕ) : ℝ) + 1) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hb0 hβ 2
    calc (Y : ℝ) ≤ c * ((TP6 P n : ℝ) * pP6 P n * (((Nat.log 2 (bP6 n) : ℕ) : ℝ) + 1) ^ 2) := hY'
      _ ≤ c * ((TP6 P n : ℝ) * pP6 P n * (2 * L) ^ 2) := by gcongr
      _ = _ := by ring
  have h3 := lift (le_of_lt hd0) hdN hTp (by positivity) h2
  exact fin hd0 (by have := le_trans (le_of_lt hd0) hdN; positivity) hc h3

private theorem p_lt_G (P : Prm) (n : ℕ) (hb : bP6 n < 2 ^ (Nat.log 2 (bP6 n) + 1)) :
    pP6 P n < 2 ^ ((P.x + 8) * (Nat.log 2 (bP6 n) + 1)) := by
  set β := Nat.log 2 (bP6 n)
  have hpw : pP6 P n < 2 ^ (3 + (1 + P.x) * (β + 1)) := by
    have e1 : pP6 P n = 6 * bP6 n ^ (1 + P.x) := rfl
    have e2 : bP6 n ^ (1 + P.x) < (2 ^ (β + 1)) ^ (1 + P.x) :=
      Nat.pow_lt_pow_left hb (by omega)
    rw [← pow_mul, Nat.mul_comm] at e2
    rw [pow_add, e1]
    have : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  exact hpw.trans_le (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

private theorem cU6_div_nonneg (P : Prm) (n D : ℕ) : 0 ≤ cU6 P n 2 / ((D : ℝ) + 1) := by
  have hcU : cU6 P n 2 = ((TP6 P n : ℝ) * pP6 P n) * Ncost6 P n *
      (Real.log (IntMul.lg n) + 1) ^ 2 := rfl
  have hdl := dl_le_Ncost6 P n
  have h1 : (0 : ℝ) ≤ dP6 P n := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ ℓP6 P n := Nat.cast_nonneg _
  have : (0 : ℝ) ≤ Ncost6 P n := by linarith
  rw [hcU]; positivity

private theorem le_addL {a K1 K2 U : ℝ} (h : a ≤ K1 * U) (hU : 0 ≤ U) (h2 : 0 ≤ K2) :
    a ≤ (K1 + K2) * U := by nlinarith

private theorem le_addR {a K1 K2 U : ℝ} (h : a ≤ K2 * U) (hU : 0 ≤ U) (h1 : 0 ≤ K1) :
    a ≤ (K1 + K2) * U := by nlinarith

/-- `AKerNeedA6` from `axANum_ev`, `aSide_at`, `akCond_at`, and `kerA_le`. -/
theorem solution (P : IntMul.Kappa.R6.Prm) (hP : P.Ok) : J6Seg.Ax.AKerNeedA6 P := by
  obtain ⟨n₁, hN⟩ := axANum_ev P hP
  refine ⟨KAs P + KKA P, 2, max n₁ (2 ^ 64), add_nonneg (KAs_nonneg P) (KKA_nonneg P), ?_⟩
  intro n hn src hsrc D hD k hk
  have h := hN n (le_of_max_le_left hn) src hsrc D hD k hk
  have hp64 : 64 ≤ pP6 P n := by
    have hb : 64 ≤ bP6 n := lg_ge 64 (le_of_max_le_right hn)
    have : bP6 n ≤ bP6 n ^ (1 + P.x) := Nat.le_self_pow (by omega) _
    show 64 ≤ 6 * bP6 n ^ (1 + P.x)
    omega
  have hS := aSide_at P h hD
  have hC := akCond_at P h hp64
  intro p s t α H pk b w f pre post M K
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hS
  have hU := cU6_div_nonneg P n D
  have hKA := KAs_nonneg P
  have hKK := KKA_nonneg P
  refine ⟨_, _, _, _, _, _, _, _, _, _, hC, le_addL a1 hU hKK, le_addL a2 hU hKK,
    le_addL a3 hU hKK, le_addL a4 hU hKK, le_addL a5 hU hKK, le_addL a6 hU hKK,
    le_addL a7 hU hKK, le_addL a8 hU hKK, ?_⟩
  have g := h.num
  have hT : pre * t * post = TP6 P n := g.tot
  have htM : t = M * 8 * (2 * H) := h.tM
  have hR : pre * (M * 8) * post * (2 * H) = TP6 P n := by rw [← hT, htM]; ring
  have hM0 : 0 < M := h.M0
  have hfl : ∀ c : ℕ, ⌊(c : ℝ) + 2⌋₊ = c + 2 := fun c => by
    rw [show (c : ℝ) + 2 = ((c + 2 : ℕ) : ℝ) by push_cast; ring]; exact Nat.floor_natCast _
  rw [hfl, tabsT_len _ _ (aTabG_length p s t α H pk b)]
  have hk := kerA_le (p := p) (H := H) (WA := J6A.WA p α H) (pre := pre) (nc := M * 8)
    (post := post) (T := TP6 P n) (G := (P.x + 8) * (Nat.log 2 (bP6 n) + 1)) (f := f)
    hp64 h.H1 h.Hp h.Ww h.f8 g.pre1 (by omega) g.post1 hR (p_lt_G P n g.bβ)
    (by
      have hx := hP.x_ge
      have h1 : 1 ≤ Nat.log 2 (bP6 n) + 1 := Nat.succ_pos _
      have h9 : 9 ≤ P.x + 8 := by omega
      calc 8 ≤ 9 := by decide
        _ ≤ (P.x + 8) * 1 := by omega
        _ ≤ (P.x + 8) * (Nat.log 2 (bP6 n) + 1) := Nat.mul_le_mul_left _ h1)
  have hk' := hk.trans (le_of_eq (show 10 ^ 16 * CfA * (TP6 P n * p *
      ((P.x + 8) * (Nat.log 2 (bP6 n) + 1)) ^ 2) = (10 ^ 16 * CfA * (P.x + 8) ^ 2) *
      (TP6 P n * p * (Nat.log 2 (bP6 n) + 1) ^ 2) by ring))
  refine le_addR (toU2 P hD hk' ?_) hU hKA
  exact le_of_eq (by unfold KKA; push_cast; ring)

end
