-- Prove2me | solution 1 for NeedPersuasion.FirstBest.theorem_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:27:29.337556+00:00
-- url     : https://prove2.me/submissions/b96bca1f-2a74-417b-8113-745669526aef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects
import Theorems.Thm_NeedPersuasion_FirstBest_theorem_1
import Theorems.Thm_NeedPersuasion_FirstBest_theorem_2
import Theorems.Thm_NeedPersuasion_FirstBest_lemma_2
import Theorems.Thm_NeedPersuasion_FirstBest_lemma_2_lex
import Theorems.Thm_NeedPersuasion_FirstBest_lemma_5_1
import Theorems.Thm_NeedPersuasion_FirstBest_lemma_6
import Theorems.Thm_NeedPersuasion_FirstBest_g_unique_root

open NeedPersuasion.FirstBest

set_option linter.unusedSectionVars false

namespace T6Red

/-! ## Abstract facts about lexicographic maximizers -/

lemma lex_sub_eq {S T : Set (ℕ → ℝ)} {f h : (ℕ → ℝ) → ℝ} (hST : S ⊆ T)
    (hsub : lexArgmax T f h ⊆ S) (hne : (lexArgmax T f h).Nonempty) :
    lexArgmax S f h = lexArgmax T f h := by
  obtain ⟨p, hpT⟩ := hne
  have hpS := hsub hpT
  ext q
  constructor
  · rintro ⟨hqS, hqf, hqh⟩
    have h1 : f p ≤ f q := hqf p hpS
    have h2 : f q ≤ f p := hpT.2.1 q (hST hqS)
    have hfp : f p = f q := le_antisymm h1 h2
    refine ⟨hST hqS, fun r hr => le_trans (hpT.2.1 r hr) h1, fun r hr hfr => ?_⟩
    have h3 : h r ≤ h p := hpT.2.2 r hr (by rw [hfr, hfp])
    have h4 : h p ≤ h q := hqh p hpS hfp
    linarith
  · intro hq
    exact ⟨hsub hq, fun r hr => hq.2.1 r (hST hr), fun r hr hfr => hq.2.2 r (hST hr) hfr⟩

lemma lex_mix {S T : Set (ℕ → ℝ)} {f h : (ℕ → ℝ) → ℝ} {p q : ℕ → ℝ} (hST : S ⊆ T)
    (hp : p ∈ lexArgmax S f h) (hq : q ∈ lexArgmax T f h)
    (t : ℝ) (ht0 : 0 < t) (z : ℕ → ℝ) (hzS : z ∈ S)
    (hfz : f z = (1 - t) * f p + t * f q) (hhz : h z = (1 - t) * h p + t * h q) :
    p ∈ lexArgmax T f h := by
  have hfq : f q ≤ f p := by
    have h1 := hp.2.1 z hzS
    rw [hfz] at h1
    nlinarith
  have hfpq : f p ≤ f q := hq.2.1 p (hST hp.1)
  have hfeq : f p = f q := le_antisymm hfpq hfq
  have hzf : f z = f p := by rw [hfz, ← hfeq]; ring
  have hhq : h q ≤ h p := by
    have h1 := hp.2.2 z hzS hzf
    rw [hhz] at h1
    nlinarith
  refine ⟨hST hp.1, fun r hr => le_trans (hq.2.1 r hr) hfq, fun r hr hfr => ?_⟩
  have : h r ≤ h q := hq.2.2 r hr (by rw [hfr, hfeq])
  linarith

/-! ## optSet as a lexicographic argmax -/

noncomputable def Fθ (M : Model) (θ : ℝ) : (ℕ → ℝ) → ℝ :=
  if θ = 0 then WH M else if θ = 1 then WL M else W M θ

noncomputable def Hθ (M : Model) (θ : ℝ) : (ℕ → ℝ) → ℝ :=
  if θ = 0 then WL M else if θ = 1 then WH M else fun _ => 0

lemma optSet_eq (M : Model) (S : Set (ℕ → ℝ)) (θ : ℝ) :
    optSet M S θ = lexArgmax S (Fθ M θ) (Hθ M θ) := by
  unfold optSet Fθ Hθ
  split_ifs
  · rfl
  · rfl
  · ext π; simp [argmaxW, lexArgmax]

lemma opt_le (M : Model) (S : Set (ℕ → ℝ)) (θ : ℝ) (π : ℕ → ℝ) (hπ : π ∈ optSet M S θ) :
    ∀ π' ∈ S, W M θ π' ≤ W M θ π := by
  intro π' hπ'
  unfold optSet at hπ
  split_ifs at hπ with h0 h1
  · subst h0; have := hπ.2.1 π' hπ'; simp [W]; linarith
  · subst h1; have := hπ.2.1 π' hπ'; simp [W]; linarith
  · exact hπ.2 π' hπ'

lemma opt_mem (M : Model) (S : Set (ℕ → ℝ)) (θ : ℝ) (π : ℕ → ℝ) (hπ : π ∈ optSet M S θ) :
    π ∈ S := by
  unfold optSet at hπ
  split_ifs at hπ
  · exact hπ.1
  · exact hπ.1
  · exact hπ.1

lemma opt_PE (M : Model) (S : Set (ℕ → ℝ)) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (π : ℕ → ℝ) (hπ : π ∈ optSet M S θ) : ParetoEfficientIn M S π := by
  refine ⟨opt_mem M S θ π hπ, fun π' hπ' hdom => ?_⟩
  obtain ⟨⟨hL, hH⟩, hstr⟩ := hdom
  unfold optSet at hπ
  split_ifs at hπ with h0 h1
  · have e1 := hπ.2.1 π' hπ'
    have e2 := hπ.2.2 π' hπ' (le_antisymm e1 hH)
    rcases hstr with h | h <;> linarith
  · have e1 := hπ.2.1 π' hπ'
    have e2 := hπ.2.2 π' hπ' (le_antisymm e1 hL)
    rcases hstr with h | h <;> linarith
  · have e := hπ.2 π' hπ'
    simp only [W] at e
    have ht0 : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm h0)
    have ht1 : θ < 1 := lt_of_le_of_ne hθ.2 h1
    rcases hstr with h | h <;> nlinarith

/-! ## Model facts -/

section model
variable (M : Model) (hM : M.Standing)
include hM

lemma lam_pos : 0 < M.lam := by
  obtain ⟨h1, h2, -⟩ := hM; unfold Model.lam; linarith

lemma lamH_lt_one : M.lamH < 1 := by
  obtain ⟨h1, h2, h3, -⟩ := hM; unfold Model.lam at h3; linarith

lemma dec_le (n : ℕ) : 0 ≤ M.uL n - M.uL (n + 1) ∧
    M.uL n - M.uL (n + 1) ≤ M.uL 0 - M.uL 1 := by
  obtain ⟨-, -, -, -, -, -, -, hA, -, hC⟩ := hM
  refine ⟨by have := hA (Nat.lt_succ_self n); linarith, ?_⟩
  exact hC (Nat.zero_le n)

lemma abs_uL_le (n : ℕ) : |M.uL n| ≤ |M.uL 0| + n * (M.uL 0 - M.uL 1) := by
  have hD := (dec_le M hM 0).1
  have hup : M.uL n ≤ M.uL 0 := by
    obtain ⟨-, -, -, -, -, -, -, hA, -, -⟩ := hM
    exact hA.antitone (Nat.zero_le n)
  have hlo : M.uL 0 - n * (M.uL 0 - M.uL 1) ≤ M.uL n := by
    induction n with
    | zero => simp
    | succ k ih =>
      have := (dec_le M hM k).2
      push_cast
      have hk : M.uL k ≤ M.uL 0 := by
        obtain ⟨-, -, -, -, -, -, -, hA, -, -⟩ := hM
        exact hA.antitone (Nat.zero_le k)
      linarith [ih hk]
  rw [abs_le]
  constructor
  · have := neg_abs_le (M.uL 0)
    have : (0 : ℝ) ≤ n * (M.uL 0 - M.uL 1) := mul_nonneg (Nat.cast_nonneg n) hD
    linarith
  · have := le_abs_self (M.uL 0)
    have : (0 : ℝ) ≤ n * (M.uL 0 - M.uL 1) := mul_nonneg (Nat.cast_nonneg n) hD
    linarith

lemma summable_shift (π : ℕ → ℝ) (hπ : π ∈ PiAP M) :
    Summable (fun n => π (n + 1) * M.uL n) := by
  obtain ⟨hnn, hsum, -, hsL, -⟩ := hπ
  have h1 : Summable (fun n => |π (n + 1) * M.uL (n + 1)|) :=
    ((summable_nat_add_iff 1).mpr hsL).abs
  have h2 : Summable (fun n => π (n + 1)) := (summable_nat_add_iff 1).mpr hsum.summable
  refine Summable.of_norm_bounded (h1.add (h2.mul_left (M.uL 0 - M.uL 1))) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hnn (n + 1))]
  have hd := dec_le M hM n
  have : |M.uL n| ≤ |M.uL (n + 1)| + (M.uL 0 - M.uL 1) := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (M.uL (n + 1)); linarith
    · have := le_abs_self (M.uL (n + 1)); linarith
  have := mul_le_mul_of_nonneg_left this (hnn (n + 1))
  linarith

lemma summable_WL (π : ℕ → ℝ) (hπ : π ∈ PiAP M) :
    Summable (fun n => (π (n + 1) - M.lamH * π n) * M.uL n) := by
  have := (summable_shift M hM π hπ).sub (hπ.2.2.2.1.mul_left M.lamH)
  refine this.congr (fun n => ?_)
  ring

lemma summable_L (π : ℕ → ℝ) (hπ : π ∈ PiAP M) :
    Summable (fun n => (M.lam * π n - π (n + 1)) * M.uL n) := by
  have := (hπ.2.2.2.1.mul_left M.lam).sub (summable_shift M hM π hπ)
  refine this.congr (fun n => ?_)
  ring

end model

/-! ## Mixtures -/

def mix (p q : ℕ → ℝ) (t : ℝ) : ℕ → ℝ := fun n => (1 - t) * p n + t * q n

lemma tsum_mix {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (t : ℝ) :
    ∑' n, ((1 - t) * a n + t * b n) = (1 - t) * ∑' n, a n + t * ∑' n, b n := by
  rw [Summable.tsum_add (ha.mul_left _) (hb.mul_left _), tsum_mul_left, tsum_mul_left]

section mixsec
variable (M : Model) (hM : M.Standing)
include hM

lemma mix_mem (p q : ℕ → ℝ) (hp : p ∈ PiAP M) (hq : q ∈ PiAP M) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : mix p q t ∈ PiAP M := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hq
  have ht' : 0 ≤ 1 - t := by linarith
  refine ⟨fun n => ?_, ?_, fun n => ?_, ?_, ?_⟩
  · unfold mix; have := hp1 n; have := hq1 n; positivity
  · have h := (hp2.mul_left (1 - t)).add (hq2.mul_left t)
    rw [show (1 - t) * 1 + t * 1 = (1:ℝ) by ring] at h
    exact h
  · unfold mix
    obtain ⟨a1, a2⟩ := hp3 n
    obtain ⟨b1, b2⟩ := hq3 n
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left a1 ht', mul_le_mul_of_nonneg_left b1 ht0]
    · nlinarith [mul_le_mul_of_nonneg_left a2 ht', mul_le_mul_of_nonneg_left b2 ht0]
  · exact ((hp4.mul_left (1 - t)).add (hq4.mul_left t)).congr (fun n => by unfold mix; ring)
  · exact ((hp5.mul_left (1 - t)).add (hq5.mul_left t)).congr (fun n => by unfold mix; ring)

lemma WL_mix (p q : ℕ → ℝ) (hp : p ∈ PiAP M) (hq : q ∈ PiAP M) (t : ℝ) :
    WL M (mix p q t) = (1 - t) * WL M p + t * WL M q := by
  unfold WL
  rw [← tsum_mix (summable_WL M hM p hp) (summable_WL M hM q hq) t]
  congr 1; ext n; unfold mix; ring

lemma join_mix (p q : ℕ → ℝ) (hp : p ∈ PiAP M) (hq : q ∈ PiAP M) (t : ℝ) :
    joinVal M (mix p q t) = (1 - t) * joinVal M p + t * joinVal M q := by
  have := WL_mix M hM p q hp hq t
  simpa [WL, joinVal] using this

lemma leave_mix (p q : ℕ → ℝ) (hp : p ∈ PiAP M) (hq : q ∈ PiAP M) (t : ℝ) :
    leaveVal M (mix p q t) = (1 - t) * leaveVal M p + t * leaveVal M q := by
  unfold leaveVal
  rw [← tsum_mix (summable_L M hM p hp) (summable_L M hM q hq) t]
  congr 1; ext n; unfold mix; ring

lemma WH_mix (p q : ℕ → ℝ) (hp : p ∈ PiAP M) (hq : q ∈ PiAP M) (t : ℝ) :
    WH M (mix p q t) = (1 - t) * WH M p + t * WH M q := by
  unfold WH
  have := tsum_mix hp.2.2.2.2 hq.2.2.2.2 t
  rw [show (fun n => mix p q t n * M.uH n) = fun n => (1 - t) * (p n * M.uH n) + t * (q n * M.uH n)
    from by ext n; unfold mix; ring, this]
  ring

lemma F_mix (θ : ℝ) (p q : ℕ → ℝ) (hp : p ∈ PiAP M) (hq : q ∈ PiAP M) (t : ℝ) :
    Fθ M θ (mix p q t) = (1 - t) * Fθ M θ p + t * Fθ M θ q := by
  unfold Fθ
  split_ifs
  · exact WH_mix M hM p q hp hq t
  · exact WL_mix M hM p q hp hq t
  · simp only [W]; rw [WL_mix M hM p q hp hq t, WH_mix M hM p q hp hq t]; ring

lemma H_mix (θ : ℝ) (p q : ℕ → ℝ) (hp : p ∈ PiAP M) (hq : q ∈ PiAP M) (t : ℝ) :
    Hθ M θ (mix p q t) = (1 - t) * Hθ M θ p + t * Hθ M θ q := by
  unfold Hθ
  split_ifs
  · exact WL_mix M hM p q hp hq t
  · exact WH_mix M hM p q hp hq t
  · ring

end mixsec

/-! ## Threshold policies -/

noncomputable def tw (M : Model) (x : ℝ) (k : ℕ) : ℝ :=
  if k ≤ ⌊x⌋₊ then M.lam ^ k
  else M.lam ^ ⌊x⌋₊ * (M.lamH + Int.fract x * M.lamL) * M.lamH ^ (k - ⌊x⌋₊ - 1)

noncomputable def tr (M : Model) (x : ℝ) (k : ℕ) : ℝ :=
  if k < ⌊x⌋₊ then M.lam else if k = ⌊x⌋₊ then M.lamH + Int.fract x * M.lamL else M.lamH

lemma tp_eq (M : Model) (x : ℝ) :
    thresholdPolicy M x = fun k => tw M x k / ∑' j, tw M x j := rfl

lemma tw_zero (M : Model) (x : ℝ) : tw M x 0 = 1 := by
  unfold tw; simp

lemma tw_rec (M : Model) (x : ℝ) (k : ℕ) : tw M x (k + 1) = tr M x k * tw M x k := by
  unfold tw tr
  set m := ⌊x⌋₊ with hm
  rcases lt_trichotomy k m with h | h | h
  · rw [if_pos (by omega : k + 1 ≤ m), if_pos h, if_pos h.le, pow_succ]; ring
  · subst h
    rw [if_neg (by omega : ¬ (m + 1 ≤ m)), if_neg (lt_irrefl m), if_pos rfl, if_pos le_rfl,
      show m + 1 - m - 1 = 0 by omega, pow_zero]
    ring
  · rw [if_neg (by omega : ¬ (k + 1 ≤ m)), if_neg (by omega : ¬ (k < m)),
      if_neg (by omega : ¬ (k = m)), if_neg (by omega : ¬ (k ≤ m)),
      show k + 1 - m - 1 = (k - m - 1) + 1 by omega, pow_succ]
    ring

lemma seq_eq_of_rec (π w r : ℕ → ℝ) (c : ℝ) (h0 : π 0 = c * w 0)
    (hπ : ∀ k, π (k + 1) = r k * π k) (hw : ∀ k, w (k + 1) = r k * w k) :
    ∀ k, π k = c * w k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih => rw [hπ, hw, ih]; ring

lemma eq_div_tsum_of_rep (π w : ℕ → ℝ) (hsum : HasSum π 1) (hp0 : 0 < π 0)
    (hrep : ∀ k, π k = π 0 * w k) : π = fun k => w k / ∑' j, w j := by
  have hfun : (fun k => (π 0)⁻¹ * π k) = w := by
    funext k; rw [hrep k]; field_simp
  have hw := hsum.mul_left (π 0)⁻¹
  rw [hfun, mul_one] at hw
  funext k
  rw [hw.tsum_eq, hrep k]
  field_simp

section thr
variable (M : Model) (hM : M.Standing)
include hM

lemma pi0_pos (π : ℕ → ℝ) (hπ : π ∈ PiAP M) : 0 < π 0 := by
  obtain ⟨hnn, hsum, hrat, -, -⟩ := hπ
  rcases (hnn 0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz : ∀ k, π k = 0 := by
      intro k
      induction k with
      | zero => exact h.symm
      | succ k ih =>
        have := (hrat k).2
        rw [ih, mul_zero] at this
        exact le_antisymm this (hnn _)
    have h0 : HasSum π 0 := by
      have : π = fun _ => 0 := funext hz
      rw [this]; exact hasSum_zero
    have := hsum.unique h0
    norm_num at this

lemma thr_data (π : ℕ → ℝ) (hπ : π ∈ PiAP M) (h : HasThresholdAtMost M π (mfi M)) :
    ∃ m : ℕ, ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ (m : ℝ) + a ≤ mfi M ∧
      (∀ k, k < m → π (k + 1) = M.lam * π k) ∧ π (m + 1) = (M.lamH + a * M.lamL) * π m ∧
      (∀ k, m < k → π (k + 1) = M.lamH * π k) ∧ 0 < π m := by
  obtain ⟨m, ⟨hlt, hgt⟩, hx⟩ := h
  have hlam := lam_pos M hM
  have hL : 0 < M.lamL := hM.1
  have hp0 := pi0_pos M hM π hπ
  have hpow : ∀ k, k ≤ m → π k = M.lam ^ k * π 0 := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih => rw [hlt k (by omega), ih (by omega)]; ring
  have hpm : 0 < π m := by rw [hpow m le_rfl]; positivity
  have hrat := hπ.2.2.1 m
  have hlamdef : M.lam = M.lamL + M.lamH := rfl
  have hden : 0 < M.lamL * π m := mul_pos hL hpm
  have hLne : M.lamL ≠ 0 := hL.ne'
  have hpmne : π m ≠ 0 := hpm.ne'
  refine ⟨m, (π (m + 1) - M.lamH * π m) / (M.lamL * π m), ?_, ?_, hx, hlt, ?_, hgt, hpm⟩
  · exact div_nonneg (by linarith [hrat.1]) hden.le
  · rw [div_le_one hden]; nlinarith [hrat.2]
  · field_simp; ring

lemma uL_nonneg_of_lt (n : ℕ) (hn : n < mfi M) : 0 ≤ M.uL n := by
  by_contra hc
  push Not at hc
  have : mfi M ≤ n := Nat.sInf_le (show n ∈ {k | M.uL k < 0} from hc)
  omega

lemma join_nonneg_thr (π : ℕ → ℝ) (hπ : π ∈ PiAP M) (h : HasThresholdAtMost M π (mfi M)) :
    0 ≤ joinVal M π := by
  obtain ⟨m, a, ha0, ha1, hx, hlt, hm1, hgt, hpm⟩ := thr_data M hM π hπ h
  have hmle : m ≤ mfi M := by
    have : (m : ℝ) ≤ mfi M := by linarith
    exact_mod_cast this
  have hL : 0 < M.lamL := hM.1
  unfold joinVal
  refine tsum_nonneg (fun n => ?_)
  rcases lt_trichotomy n m with h | h | h
  · rw [hlt n h]
    have := uL_nonneg_of_lt M hM n (by omega)
    have := hπ.1 n
    have : M.lam * π n - M.lamH * π n = M.lamL * π n := by unfold Model.lam; ring
    rw [this]; positivity
  · subst h
    rw [hm1]
    have hc : (M.lamH + a * M.lamL) * π n - M.lamH * π n = a * M.lamL * π n := by ring
    rw [hc]
    rcases ha0.lt_or_eq with ha | ha
    · have : (n : ℝ) < mfi M := by linarith
      have := uL_nonneg_of_lt M hM n (by exact_mod_cast this)
      positivity
    · rw [← ha]; simp
  · rw [hgt n h]; simp

lemma thr_glue (π : ℕ → ℝ) (hπ : π ∈ PiAP M) (h : HasThresholdAtMost M π (mfi M)) :
    ∃ x : ℝ, 0 ≤ x ∧ π = thresholdPolicy M x := by
  obtain ⟨m, a, ha0, ha1, -, hlt, hm1, hgt, hpm⟩ := thr_data M hM π hπ h
  have hp0 := pi0_pos M hM π hπ
  refine ⟨m + a, by positivity, ?_⟩
  have key : ∀ k, π (k + 1) = tr M (m + a) k * π k := by
    rcases ha1.lt_or_eq with ha1' | ha1'
    · have hfl : ⌊(m : ℝ) + a⌋₊ = m := by
        rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
      have hfr : Int.fract ((m : ℝ) + a) = a := by
        rw [Int.fract_eq_iff]; exact ⟨ha0, ha1', m, by push_cast; ring⟩
      intro k
      unfold tr
      rw [hfl, hfr]
      split_ifs with h1 h2
      · exact hlt k h1
      · subst h2; exact hm1
      · exact hgt k (by omega)
    · subst ha1'
      have hfl : ⌊(m : ℝ) + 1⌋₊ = m + 1 := by
        have := Nat.floor_natCast (R := ℝ) (m + 1)
        push_cast at this; exact this
      have hfr : Int.fract ((m : ℝ) + 1) = 0 := by
        have := Int.fract_natCast (R := ℝ) (m + 1)
        push_cast at this; exact this
      intro k
      unfold tr
      rw [hfl, hfr]
      split_ifs with h1 h2
      · rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
        · exact hlt k h
        · subst h; rw [hm1]; unfold Model.lam; ring
      · subst h2; rw [zero_mul, add_zero]; exact hgt (m + 1) (by omega)
      · exact hgt k (by omega)
  have hrep := seq_eq_of_rec π (tw M (m + a)) (tr M (m + a)) (π 0)
    (by rw [tw_zero]; ring) key (tw_rec M (m + a))
  rw [tp_eq]
  exact eq_div_tsum_of_rep π _ hπ.2.1 hp0 hrep

lemma tp_zero (k : ℕ) : thresholdPolicy M 0 k = (1 - M.lamH) * M.lamH ^ k := by
  have h0 : 0 ≤ M.lamH := hM.2.1
  have h1 := lamH_lt_one M hM
  have htw : ∀ k, tw M 0 k = M.lamH ^ k := by
    intro k
    unfold tw
    simp only [Nat.floor_zero, Int.fract_zero, zero_mul, add_zero]
    rcases k with _ | k
    · simp
    · rw [if_neg (by omega), pow_zero, one_mul, show k + 1 - 0 - 1 = k by omega, pow_succ]
      ring
  rw [tp_eq]
  simp only [htw]
  rw [tsum_geometric_of_lt_one h0 h1]
  have : (1 - M.lamH) ≠ 0 := by linarith
  field_simp

lemma tp0_mem (hSumH : Summable (fun k => M.lamH ^ k * M.uH k)) :
    thresholdPolicy M 0 ∈ PiAP M := by
  have h0 : 0 ≤ M.lamH := hM.2.1
  have h1 := lamH_lt_one M hM
  have hL : 0 < M.lamL := hM.1
  have h1' : 0 ≤ 1 - M.lamH := by linarith
  have e : thresholdPolicy M 0 = fun k => (1 - M.lamH) * M.lamH ^ k := funext (tp_zero M hM)
  rw [e]
  refine ⟨fun n => by positivity, ?_, fun n => ⟨?_, ?_⟩, ?_, ?_⟩
  · have := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - M.lamH)
    rwa [mul_inv_cancel₀ (by linarith : (1 - M.lamH) ≠ 0)] at this
  · dsimp only; apply le_of_eq; ring
  · dsimp only
    have hX : 0 ≤ (1 - M.lamH) * M.lamH ^ n := by positivity
    have : (1 - M.lamH) * M.lamH ^ (n + 1) = M.lamH * ((1 - M.lamH) * M.lamH ^ n) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hX
    unfold Model.lam; linarith
  · have hD := (dec_le M hM 0).1
    have hs1 : Summable (fun n : ℕ => M.lamH ^ n) := summable_geometric_of_lt_one h0 h1
    have hs2 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * M.lamH ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
    refine Summable.of_norm_bounded
      (((hs1.mul_left |M.uL 0|).add (hs2.mul_left (M.uL 0 - M.uL 1))).mul_left (1 - M.lamH))
      (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1', abs_of_nonneg (by positivity)]
    have hb := abs_uL_le M hM n
    have hp : 0 ≤ (1 - M.lamH) * M.lamH ^ n := by positivity
    have := mul_le_mul_of_nonneg_left hb hp
    simp only [pow_one]
    nlinarith
  · exact (hSumH.mul_left (1 - M.lamH)).congr (fun n => by ring)

lemma leave_tp0 : leaveValx M 0 = M.lamL * g M M.lamH := by
  unfold leaveValx leaveVal g
  simp only [tp_zero M hM]
  rw [← tsum_mul_left]
  congr 1; ext n; unfold Model.lam; ring

lemma WL_tp0 : WL M (thresholdPolicy M 0) = 0 := by
  unfold WL
  have : ∀ n, (thresholdPolicy M 0 (n + 1) - M.lamH * thresholdPolicy M 0 n) * M.uL n = 0 := by
    intro n; rw [tp_zero M hM, tp_zero M hM]; ring
  simp [this]

end thr

end T6Red

open T6Red in
theorem solution (M : Model) (hM : M.Standing)
    (hExist : M.lam < 1 ∨ (Filter.Tendsto M.uL Filter.atTop Filter.atBot ∧
      Filter.Tendsto M.uH Filter.atTop Filter.atBot))
    (hSumH : Summable (fun k => M.lamH ^ k * M.uH k))
    (Λ : ℝ) (hΛ : Λ ∈ Set.Ioo (0 : ℝ) 1 ∧ g M Λ = 0) :
    (Λ ≤ M.lamH → ∀ θ ∈ Set.Icc (0 : ℝ) 1, smSet M θ = apSet M θ) ∧
    (M.lamH < Λ → ∃ θbar ∈ Set.Ioc (0 : ℝ) 1,
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, θbar < θ → smSet M θ = apSet M θ) ∧
      ∀ θ ∈ Set.Ico (0 : ℝ) θbar, ∀ θ' ∈ Set.Ico (0 : ℝ) θbar, smSet M θ = smSet M θ') := by
  classical
  have hT1 := NeedPersuasion.FirstBest.theorem_1 M hM
  have hT2 := NeedPersuasion.FirstBest.theorem_2 M hM
  have hL2 := NeedPersuasion.FirstBest.lemma_2 M hM hExist hSumH
  have hLex := NeedPersuasion.FirstBest.lemma_2_lex M hM hExist hSumH
  have hL6 := (NeedPersuasion.FirstBest.lemma_6 M hM).1
  have hg := (NeedPersuasion.FirstBest.g_unique_root M hM).1
  have hlH1 := lamH_lt_one M hM
  have hlH0 : 0 ≤ M.lamH := hM.2.1
  have hlL : 0 < M.lamL := hM.1
  -- non-emptiness of the optimal sets
  have hne : ∀ θ ∈ Set.Icc (0 : ℝ) 1, (smSet M θ).Nonempty ∧ (apSet M θ).Nonempty := by
    intro θ hθ
    unfold smSet apSet optSet
    split_ifs with h0 h1
    · exact ⟨hLex.1, hLex.2.2.1⟩
    · exact ⟨hLex.2.1, hLex.2.2.2⟩
    · exact hL2 θ hθ
  -- threshold structure of optimal policies
  have hap_thr : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ π ∈ apSet M θ,
      π ∈ PiAP M ∧ 0 ≤ joinVal M π ∧ ∃ x, 0 ≤ x ∧ π = thresholdPolicy M x := by
    intro θ hθ π hπ
    have hPE := opt_PE M _ θ hθ π hπ
    have hth := (hT2 π hPE).2
    exact ⟨hPE.1, join_nonneg_thr M hM π hPE.1 hth, thr_glue M hM π hPE.1 hth⟩
  have hsm_thr : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ π ∈ smSet M θ,
      π ∈ PiAP M ∧ ∃ x, 0 ≤ x ∧ π = thresholdPolicy M x := by
    intro θ hθ π hπ
    have hPE := opt_PE M _ θ hθ π hπ
    have hth := (hT1 π hPE).2
    exact ⟨hPE.1.1, thr_glue M hM π hPE.1.1 hth⟩
  have hL0 : leaveValx M 0 = M.lamL * g M M.lamH := leave_tp0 M hM
  have hup : ∀ x y : ℝ, 0 ≤ x → x ≤ y → leaveValx M x ≤ 0 → leaveValx M y ≤ 0 := by
    intro x y hx hxy hLx
    rcases hxy.lt_or_eq with h | h
    · by_contra hc
      push Not at hc
      have := hL6 x y hx h hc.le
      linarith
    · rw [← h]; exact hLx
  have hEq : ∀ θ ∈ Set.Icc (0 : ℝ) 1, apSet M θ ⊆ PiSM M → smSet M θ = apSet M θ := by
    intro θ hθ hsub
    have hne' := (hne θ hθ).2
    unfold smSet apSet at *
    rw [optSet_eq] at hsub hne' ⊢
    rw [optSet_eq]
    exact lex_sub_eq (fun π hπ => hπ.1) hsub hne'
  constructor
  · -- Case 1: Λ ≤ λ_H
    intro hle θ hθ
    apply hEq θ hθ
    intro π hπ
    obtain ⟨hmem, hJ, x, hx0, rfl⟩ := hap_thr θ hθ π hπ
    have hgle : g M M.lamH ≤ 0 := by
      rcases hle.lt_or_eq with h | h
      · have := hg ⟨hΛ.1.1.le, hΛ.1.2⟩ ⟨hlH0, hlH1⟩ h
        linarith [hΛ.2]
      · rw [← h, hΛ.2]
    have h0 : leaveValx M 0 ≤ 0 := by
      rw [hL0]; exact mul_nonpos_of_nonneg_of_nonpos hlL.le hgle
    exact ⟨hmem, hJ, hup 0 x le_rfl hx0 h0⟩
  · -- Case 2: λ_H < Λ
    intro hlt
    have hgpos : 0 < g M M.lamH := by
      have := hg ⟨hlH0, hlH1⟩ ⟨hΛ.1.1.le, hΛ.1.2⟩ hlt
      linarith [hΛ.2]
    have hL0pos : 0 < leaveValx M 0 := by rw [hL0]; positivity
    rcases hlH0.lt_or_eq with hHpos | hH0
    · -- λ_H > 0
      have hWHanti := NeedPersuasion.FirstBest.lemma_5_1 M hM hHpos hSumH
      set A : Set ℝ := {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ π ∈ apSet M θ, π ∈ PiSM M} with hA
      -- (U) upward closedness
      have hU : ∀ θ1 ∈ A, ∀ θ2 ∈ Set.Icc (0 : ℝ) 1, θ1 < θ2 → apSet M θ2 ⊆ PiSM M := by
        rintro θ1 ⟨hθ1, π1, hπ1, hπ1SM⟩ θ2 hθ2 h12 π2 hπ2
        have hPE1 := opt_PE M _ θ1 hθ1 π1 hπ1
        have hm2 := opt_mem M _ θ2 π2 hπ2
        have e1 := opt_le M _ θ1 π1 hπ1 π2 hm2
        have e2 := opt_le M _ θ2 π2 hπ2 π1 (opt_mem M _ θ1 π1 hπ1)
        have hWH : WH M π2 ≤ WH M π1 := by
          by_contra hc
          push Not at hc
          simp only [W] at e1 e2
          have key : 0 ≤ (θ2 - θ1) * ((WL M π2 - WL M π1) - (WH M π2 - WH M π1)) := by
            nlinarith
          have hd : 0 ≤ (WL M π2 - WL M π1) - (WH M π2 - WH M π1) := by
            by_contra hneg
            push Not at hneg
            have := mul_neg_of_pos_of_neg (sub_pos.mpr h12) hneg
            linarith
          have hWL : WL M π1 < WL M π2 := by linarith
          exact hPE1.2 π2 hm2 ⟨⟨hWL.le, hc.le⟩, Or.inl hWL⟩
        obtain ⟨-, -, x1, hx1, rfl⟩ := hap_thr θ1 hθ1 π1 hπ1
        obtain ⟨hm2', hJ2, x2, hx2, rfl⟩ := hap_thr θ2 hθ2 π2 hπ2
        have hx12 : x1 ≤ x2 := by
          by_contra hc
          push Not at hc
          have := hWHanti (Set.mem_Ici.mpr hx2) (Set.mem_Ici.mpr hx1) hc
          exact absurd hWH (not_le.mpr this)
        exact ⟨hm2', hJ2, hup x1 x2 hx1 hx12 hπ1SM.2.2⟩
      -- (Gap) small weights are not in A
      have hGap : ∃ ε > 0, ∀ θ ∈ A, ε ≤ θ := by
        have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
        obtain ⟨ρ, hρ⟩ := (hne 0 h0I).1
        obtain ⟨-, xρ, hxρ, hρeq⟩ := hsm_thr 0 h0I ρ hρ
        have hρSM := opt_mem M _ 0 ρ hρ
        have hLρ : leaveValx M xρ ≤ 0 := by
          have := hρSM.2.2; rw [hρeq] at this; exact this
        have hxpos : 0 < xρ := by
          rcases hxρ.lt_or_eq with h | h
          · exact h
          · rw [← h] at hLρ; linarith
        have hWHlt : WH M ρ < WHx M 0 := by
          rw [hρeq]; exact hWHanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hxρ) hxpos
        have hρmax : ∀ π ∈ PiSM M, WH M π ≤ WH M ρ := by
          intro π hπ
          have := opt_le M _ 0 ρ hρ π hπ
          simpa [W] using this
        obtain ⟨σ, hσ⟩ := (hL2 1 ⟨zero_le_one, le_rfl⟩).2
        have hσmax : ∀ π ∈ PiAP M, WL M π ≤ WL M σ := by
          intro π hπ
          have := hσ.2 π hπ
          simpa [W] using this
        have htp0 := tp0_mem M hM hSumH
        have hWL0 := WL_tp0 M hM
        have hWH0 : WH M (thresholdPolicy M 0) = WHx M 0 := rfl
        have hδ : 0 < WHx M 0 - WH M ρ := by linarith
        have hML : 0 ≤ WL M σ := by have := hσmax _ htp0; linarith
        refine ⟨(WHx M 0 - WH M ρ) / (WL M σ + (WHx M 0 - WH M ρ)), by positivity, ?_⟩
        rintro θ ⟨hθ, π, hπ, hπSM⟩
        by_contra hc
        push Not at hc
        rw [lt_div_iff₀ (by linarith)] at hc
        have e := opt_le M _ θ π hπ _ htp0
        simp only [W] at e
        rw [hWL0, hWH0] at e
        have h1 := hσmax π hπSM.1
        have h2 := hρmax π hπSM
        have i1 : θ * WL M π ≤ θ * WL M σ := mul_le_mul_of_nonneg_left h1 hθ.1
        have i2 : (1 - θ) * WH M π ≤ (1 - θ) * WH M ρ :=
          mul_le_mul_of_nonneg_left h2 (by linarith [hθ.2])
        nlinarith
      -- (Const) below the threshold, the optimal signaling mechanism binds (LEAVE)
      have hConst : ∀ θ ∈ Set.Icc (0 : ℝ) 1, θ ∉ A → ∀ π ∈ smSet M θ,
          ∃ x, 0 ≤ x ∧ π = thresholdPolicy M x ∧ leaveValx M x = 0 := by
        intro θ hθ hnA π hπ
        obtain ⟨hπAP, x, hx, hπeq⟩ := hsm_thr θ hθ π hπ
        have hπSM := opt_mem M _ θ π hπ
        refine ⟨x, hx, hπeq, ?_⟩
        have hle : leaveValx M x ≤ 0 := by
          have := hπSM.2.2; rw [hπeq] at this; exact this
        refine le_antisymm hle ?_
        by_contra hc
        push Not at hc
        have hLπ : leaveVal M π < 0 := by rw [hπeq]; exact hc
        apply hnA
        refine ⟨hθ, π, ?_, hπSM⟩
        obtain ⟨q, hq⟩ := (hne θ hθ).2
        obtain ⟨hqAP, hqJ, -⟩ := hap_thr θ hθ q hq
        set a := leaveVal M π with ha
        set b := leaveVal M q with hb
        have hpos : 0 < -a + |b| := by have := abs_nonneg b; linarith
        set t := (-a) / (-a + |b|) with ht
        have ht0 : 0 < t := div_pos (by linarith) hpos
        have ht1 : t ≤ 1 := by rw [ht, div_le_one hpos]; linarith [abs_nonneg b]
        have hzAP := mix_mem M hM π q hπAP hqAP t ht0.le ht1
        have hzSM : mix π q t ∈ PiSM M := by
          refine ⟨hzAP, ?_, ?_⟩
          · rw [join_mix M hM π q hπAP hqAP t]
            have := hπSM.2.1
            have : 0 ≤ 1 - t := by linarith
            positivity
          · rw [leave_mix M hM π q hπAP hqAP t]
            have e1 : 1 - t = |b| / (-a + |b|) := by
              rw [ht]; field_simp; ring
            rw [e1, ht, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
            apply div_nonpos_of_nonpos_of_nonneg _ hpos.le
            have := mul_nonneg (by linarith : (0:ℝ) ≤ -a) (sub_nonneg.mpr (le_abs_self b))
            nlinarith
        have hπ' := hπ
        have hq' := hq
        unfold smSet at hπ'
        unfold apSet at hq' ⊢
        rw [optSet_eq] at hπ' hq' ⊢
        exact lex_mix (fun p hp => hp.1) hπ' hq' t ht0 (mix π q t) hzSM
          (F_mix M hM θ π q hπAP hqAP t) (H_mix M hM θ π q hπAP hqAP t)
      have hsmEq : ∀ θ ∈ Set.Icc (0 : ℝ) 1, θ ∉ A → ∀ θ' ∈ Set.Icc (0 : ℝ) 1, θ' ∉ A →
          smSet M θ = smSet M θ' := by
        have aux : ∀ θ ∈ Set.Icc (0 : ℝ) 1, θ ∉ A → ∀ θ' ∈ Set.Icc (0 : ℝ) 1, θ' ∉ A →
            smSet M θ ⊆ smSet M θ' := by
          intro θ hθ hnA θ' hθ' hnA' π hπ
          obtain ⟨π', hπ'⟩ := (hne θ' hθ').1
          obtain ⟨x, hx, hπeq, hLx⟩ := hConst θ hθ hnA π hπ
          obtain ⟨x', hx', hπ'eq, hLx'⟩ := hConst θ' hθ' hnA' π' hπ'
          have hxx : x = x' := by
            by_contra hne'
            rcases lt_or_gt_of_ne hne' with h | h
            · have := hL6 x x' hx h (by rw [hLx'])
              rw [hLx, hLx'] at this
              exact lt_irrefl _ this
            · have := hL6 x' x hx' h (by rw [hLx])
              rw [hLx, hLx'] at this
              exact lt_irrefl _ this
          rw [hπeq, hxx, ← hπ'eq]
          exact hπ'
        intro θ hθ hnA θ' hθ' hnA'
        exact Set.Subset.antisymm (aux θ hθ hnA θ' hθ' hnA') (aux θ' hθ' hnA' θ hθ hnA)
      obtain ⟨ε, hε, hεA⟩ := hGap
      by_cases hAne : A.Nonempty
      · have hbdd : BddBelow A := ⟨0, fun θ hθ => hθ.1.1⟩
        have hle1 : sInf A ≤ 1 := by
          obtain ⟨θ0, hθ0⟩ := hAne
          exact (csInf_le hbdd hθ0).trans hθ0.1.2
        refine ⟨sInf A, ⟨lt_of_lt_of_le hε (le_csInf hAne hεA), hle1⟩, ?_, ?_⟩
        · intro θ hθ hgt
          obtain ⟨θ1, hθ1, h1⟩ := exists_lt_of_csInf_lt hAne hgt
          exact hEq θ hθ (hU θ1 hθ1 θ hθ h1)
        · intro θ hθ θ' hθ'
          have hnA : ∀ φ, φ < sInf A → φ ∉ A := fun φ hφ h =>
            absurd (csInf_le hbdd h) (not_le.mpr hφ)
          exact hsmEq θ ⟨hθ.1, by linarith [hθ.2]⟩ (hnA θ hθ.2)
            θ' ⟨hθ'.1, by linarith [hθ'.2]⟩ (hnA θ' hθ'.2)
      · refine ⟨1, ⟨one_pos, le_rfl⟩, fun θ hθ h => absurd h (not_lt.mpr hθ.2), ?_⟩
        intro θ hθ θ' hθ'
        have hnA : ∀ φ, φ ∉ A := fun φ h => hAne ⟨φ, h⟩
        exact hsmEq θ ⟨hθ.1, hθ.2.le⟩ (hnA θ) θ' ⟨hθ'.1, hθ'.2.le⟩ (hnA θ')
    · -- λ_H = 0: W_H ≡ 0, so sm(θ) does not depend on θ
      refine ⟨1, ⟨one_pos, le_rfl⟩, fun θ hθ h => absurd h (not_lt.mpr hθ.2), ?_⟩
      have hWH : ∀ π, WH M π = 0 := fun π => by simp [WH, ← hH0]
      have key : ∀ θ ∈ Set.Ico (0 : ℝ) 1,
          smSet M θ = {π | π ∈ PiSM M ∧ ∀ π' ∈ PiSM M, WL M π' ≤ WL M π} := by
        intro θ hθ
        have h1 : θ ≠ 1 := ne_of_lt hθ.2
        ext π
        unfold smSet optSet
        split_ifs with h0
        · simp [lexArgmax, hWH]
        · simp only [argmaxW, W, hWH, Set.mem_ofPred_eq, mul_zero, add_zero]
          have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm h0)
          constructor
          · rintro ⟨h, h'⟩
            exact ⟨h, fun π' hπ' => by have := h' π' hπ'; nlinarith⟩
          · rintro ⟨h, h'⟩
            exact ⟨h, fun π' hπ' => by have := h' π' hπ'; nlinarith⟩
      intro θ hθ θ' hθ'
      rw [key θ hθ, key θ' hθ']
