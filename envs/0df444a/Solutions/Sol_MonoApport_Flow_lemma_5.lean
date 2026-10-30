-- Prove2me | solution 1 for MonoApport.Flow.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:41:31.031729+00:00
-- url     : https://prove2.me/submissions/06f56ed0-16cc-4f6d-b178-e32cf227c594

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting
import Theorems.Thm_MonoApport_Flow_lemma_3

open MonoApport.Flow Finset

namespace MonoAux

variable {n : ℕ} (p : Fin n → ℕ)

noncomputable def fl (t : ℕ) (i : Fin n) : ℕ := ⌊(p i : ℝ) * t / totalPop p⌋₊
noncomputable def cl (t : ℕ) (i : Fin n) : ℕ := ⌈(p i : ℝ) * t / totalPop p⌉₊

variable {p}

lemma P_pos (hp : IsPop p) : (0 : ℝ) < totalPop p := by
  have : 0 < totalPop p := by
    unfold totalPop
    have hn : Nonempty (Fin n) := ⟨⟨0, hp.1⟩⟩
    obtain ⟨i⟩ := hn
    exact lt_of_lt_of_le (hp.2 i) (Finset.single_le_sum (fun j _ => Nat.zero_le (p j)) (mem_univ i))
  exact_mod_cast this

lemma P_pos' (hp : IsPop p) : 0 < totalPop p := by exact_mod_cast P_pos hp

lemma q_nonneg (hp : IsPop p) (t : ℕ) (i : Fin n) : 0 ≤ (p i : ℝ) * t / totalPop p :=
  div_nonneg (by positivity) (P_pos hp).le

lemma sum_q (hp : IsPop p) (t : ℝ) : ∑ i, (p i : ℝ) * t / totalPop p = t := by
  rw [← Finset.sum_div, ← Finset.sum_mul]
  have : (∑ i, (p i : ℝ)) = totalPop p := by unfold totalPop; push_cast; rfl
  rw [this]; field_simp [(P_pos hp).ne']

lemma fl_le (hp : IsPop p) (t : ℕ) (i : Fin n) : (fl p t i : ℝ) ≤ (p i : ℝ) * t / totalPop p :=
  Nat.floor_le (q_nonneg hp t i)

lemma lt_fl_add_one (t : ℕ) (i : Fin n) : (p i : ℝ) * t / totalPop p < fl p t i + 1 :=
  Nat.lt_floor_add_one _

lemma cl_le_fl_add_one (t : ℕ) (i : Fin n) : cl p t i ≤ fl p t i + 1 :=
  Nat.ceil_le_floor_add_one _

lemma fl_le_cl (t : ℕ) (i : Fin n) : fl p t i ≤ cl p t i := Nat.floor_le_ceil _

lemma fl_mono (hp : IsPop p) {t t' : ℕ} (h : t ≤ t') (i : Fin n) : fl p t i ≤ fl p t' i := by
  unfold fl
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ (P_pos hp).le
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by positivity)

lemma cl_mono (hp : IsPop p) {t t' : ℕ} (h : t ≤ t') (i : Fin n) : cl p t i ≤ cl p t' i := by
  unfold cl
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (P_pos hp).le
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by positivity)

lemma fl_mul_P (hp : IsPop p) (c : ℕ) (i : Fin n) : fl p (c * totalPop p) i = c * p i := by
  unfold fl
  have : (p i : ℝ) * ((c * totalPop p : ℕ) : ℝ) / totalPop p = ((c * p i : ℕ) : ℝ) := by
    push_cast; field_simp [(P_pos hp).ne']
  rw [this, Nat.floor_natCast]

lemma lq_eq (H k : ℕ) (i : Fin n) : lq p H k i = fl p (H + k) i := by
  unfold lq fl; push_cast; rfl

lemma K_floor_eq (t : ℕ) (i : Fin n) :
    ⌊((t : ℕ) + 1 : ℝ) * p i / totalPop p⌋₊ = fl p (t + 1) i := by
  unfold fl; push_cast; rw [mul_comm]

lemma K_ceil_eq (t : ℕ) (i : Fin n) :
    ⌈((t : ℕ) + 1 : ℝ) * p i / totalPop p⌉₊ = cl p (t + 1) i := by
  unfold cl; push_cast; rw [mul_comm]

lemma quota_floor (H : ℕ) (i : Fin n) : ⌊quota p H i⌋₊ = fl p H i := rfl
lemma quota_ceil (H : ℕ) (i : Fin n) : ⌈quota p H i⌉₊ = cl p H i := rfl

/-! ### The extended columns and `A` -/

/-- column `m` of `x`, extended by `0` beyond `L`. -/
noncomputable def xe {L : ℕ} (x : Fin n → Fin L → ℝ) (i : Fin n) (m : ℕ) : ℝ :=
  if h : m < L then x i ⟨m, h⟩ else 0

lemma A_zero {L : ℕ} (x : Fin n → Fin L → ℝ) : A x 0 = 0 := by
  funext i; simp [A]

lemma A_succ {L : ℕ} (x : Fin n → Fin L → ℝ) (T : ℕ) (i : Fin n) :
    A x (T + 1) i = A x T i + xe x i T := by
  unfold A xe
  by_cases hT : T < L
  · rw [dif_pos hT]
    have : (univ.filter (fun ℓ : Fin L => ℓ.val < T + 1)) =
        insert ⟨T, hT⟩ (univ.filter (fun ℓ : Fin L => ℓ.val < T)) := by
      ext ℓ; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
    rw [this, Finset.sum_insert (by simp), add_comm]
  · rw [dif_neg hT, add_zero]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext ℓ; simp only [mem_filter, mem_univ, true_and]; omega

lemma A_eq_range {L : ℕ} (x : Fin n → Fin L → ℝ) (T : ℕ) (i : Fin n) :
    A x T i = ∑ m ∈ range T, xe x i m := by
  induction T with
  | zero => simp [A_zero]
  | succ T ih => rw [A_succ, ih, Finset.sum_range_succ]

lemma prefix_eq_A {L : ℕ} (x : Fin n → Fin L → ℝ) (i : Fin n) (t : Fin L) :
    ∑ ℓ ∈ univ.filter (· ≤ t), x i ℓ = A x (t.val + 1) i := by
  unfold A
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext ℓ; simp only [mem_filter, mem_univ, true_and, Fin.le_iff_val_le_val]; omega

lemma xe_of_lt {L : ℕ} (x : Fin n → Fin L → ℝ) (i : Fin n) (t : Fin L) : xe x i t.val = x i t := by
  unfold xe; rw [dif_pos t.isLt]


/-! ### `k⋆` -/

lemma sum_le_sum_S (y : Fin n → ℝ) (a : Fin n → ℕ) :
    ∑ i, ((a i : ℝ) - y i) ≤ ∑ i ∈ univ.filter (fun i => y i < a i), ((a i : ℝ) - y i) := by
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · exact le_rfl
  · linarith [not_lt.mp h]

def k0 (p : Fin n → ℕ) (T : ℕ) : ℕ := (T + 1) * totalPop p - T

lemma k0_mem (hp : IsPop p) (T : ℕ) (y : Fin n → ℝ) (hy : ∑ i, y i ≤ T) :
    k0 p T ∈ {k : ℕ | 1 ≤ k ∧ (k : ℝ) ≤ ∑ i ∈ S p T y k, ((lq p T k i : ℝ) - y i)} := by
  have hP := P_pos' hp
  have h1 : T + 1 ≤ (T + 1) * totalPop p := Nat.le_mul_of_pos_right _ hP
  refine ⟨by unfold k0; omega, ?_⟩
  have hk : T + k0 p T = (T + 1) * totalPop p := by unfold k0; omega
  have hlq : ∀ i, lq p T (k0 p T) i = (T + 1) * p i := by
    intro i; rw [lq_eq, hk, fl_mul_P hp]
  refine le_trans ?_ (sum_le_sum_S y (fun i => lq p T (k0 p T) i))
  simp only [hlq]
  rw [Finset.sum_sub_distrib]
  have : (∑ i, (((T + 1) * p i : ℕ) : ℝ)) = ((T + 1) * totalPop p : ℕ) := by
    unfold totalPop; push_cast; rw [Finset.mul_sum]
  rw [this]
  have : ((k0 p T : ℕ) : ℝ) = ((T + 1) * totalPop p : ℕ) - (T : ℝ) := by
    unfold k0; rw [Nat.cast_sub (by omega)]
  rw [this]; linarith

lemma kset_nonempty (hp : IsPop p) (T : ℕ) (y : Fin n → ℝ) (hy : ∑ i, y i ≤ T) :
    {k : ℕ | 1 ≤ k ∧ (k : ℝ) ≤ ∑ i ∈ S p T y k, ((lq p T k i : ℝ) - y i)}.Nonempty :=
  ⟨_, k0_mem hp T y hy⟩

lemma kStar_mem (hp : IsPop p) (T : ℕ) (y : Fin n → ℝ) (hy : ∑ i, y i ≤ T) :
    1 ≤ kStar p T y ∧ (kStar p T y : ℝ) ≤
      ∑ i ∈ S p T y (kStar p T y), ((lq p T (kStar p T y) i : ℝ) - y i) :=
  Nat.sInf_mem (kset_nonempty hp T y hy)

lemma kStar_le (T : ℕ) (y : Fin n → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (h : (k : ℝ) ≤ ∑ i ∈ S p T y k, ((lq p T k i : ℝ) - y i)) : kStar p T y ≤ k :=
  Nat.sInf_le ⟨hk, h⟩

lemma kStar_le_k0 (hp : IsPop p) (T : ℕ) (y : Fin n → ℝ) (hy : ∑ i, y i ≤ T) :
    kStar p T y ≤ k0 p T :=
  Nat.sInf_le (k0_mem hp T y hy)

lemma tau_pos (hp : IsPop p) (T : ℕ) (y : Fin n → ℝ) (hy : ∑ i, y i ≤ T) : 1 ≤ tau p T y := by
  unfold tau; split_ifs
  · exact le_rfl
  · exact (kStar_mem hp T y hy).1

lemma tau_le (hp : IsPop p) (T : ℕ) (y : Fin n → ℝ) (hy : ∑ i, y i ≤ T) :
    tau p T y ≤ k0 p T + 1 := by
  unfold tau; split_ifs
  · omega
  · have := kStar_le_k0 hp T y hy; omega

lemma calL_eq (T : ℕ) (y : Fin n → ℝ) : calL p T y = S p T y (kStar p T y) := rfl

/-- `ℒ ∩ 𝒰` is never empty. -/
lemma LU_nonempty (hp : IsPop p) (T : ℕ) (y : Fin n → ℝ) (hy : ∑ i, y i ≤ T) :
    ∃ i, i ∈ calL p T y ∩ calU p T y := by
  by_contra hne
  push Not at hne
  obtain ⟨hk1, hk⟩ := kStar_mem hp T y hy
  set k := kStar p T y with hkdef
  have hP := P_pos hp
  have hb : ∀ i ∈ S p T y k, ((lq p T k i : ℝ) - y i) ≤ (p i : ℝ) * ((k : ℝ) - 1) / totalPop p := by
    intro i hi
    have hiU : i ∉ calU p T y := by
      intro hu; exact hne i (Finset.mem_inter.mpr ⟨hi, hu⟩)
    simp only [calU, mem_filter, mem_univ, true_and, not_lt] at hiU
    have h1 : (lq p T k i : ℝ) ≤ (p i : ℝ) * ((T : ℝ) + k) / totalPop p := by
      unfold lq; exact Nat.floor_le (div_nonneg (by positivity) hP.le)
    have : (p i : ℝ) * ((k : ℝ) - 1) / totalPop p =
        (p i : ℝ) * ((T : ℝ) + k) / totalPop p - (p i : ℝ) * ((T : ℝ) + 1) / totalPop p := by
      field_simp; ring
    rw [this]; linarith
  have h2 : ∑ i ∈ S p T y k, (p i : ℝ) * ((k : ℝ) - 1) / totalPop p ≤
      ∑ i, (p i : ℝ) * ((k : ℝ) - 1) / totalPop p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro i _ _
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    apply div_nonneg _ hP.le
    apply mul_nonneg (by positivity); linarith
  rw [sum_q hp] at h2
  have := Finset.sum_le_sum hb
  linarith

/-! ### The invariant -/

noncomputable def Dn (p : Fin n → ℕ) (T : ℕ) (y : Fin n → ℕ) (k : ℕ) : ℕ :=
  ∑ i, (fl p (T + k) i - y i)

lemma S_sum_eq (T k : ℕ) (y : Fin n → ℕ) :
    ∑ i ∈ S p T (fun j => (y j : ℝ)) k, ((lq p T k i : ℝ) - y i) = (Dn p T y k : ℝ) := by
  unfold S Dn
  rw [Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [lq_eq]
  split_ifs with h
  · have : y i ≤ fl p (T + k) i := by exact_mod_cast h.le
    rw [Nat.cast_sub this]
  · have : fl p (T + k) i ≤ y i := by exact_mod_cast (not_lt.mp h)
    rw [Nat.sub_eq_zero_of_le this]; simp

def Inv (p : Fin n → ℕ) (T : ℕ) (y : Fin n → ℕ) : Prop :=
  ∑ i, y i = T ∧ (∀ i, y i ≤ cl p T i) ∧ ∀ k, Dn p T y k ≤ k

lemma Inv.sum_le {T : ℕ} {y : Fin n → ℕ} (h : Inv p T y) : ∑ i, ((y i : ℕ) : ℝ) ≤ T := by
  have := h.1; rw [← this]; push_cast; exact le_rfl

lemma Inv_zero (hp : IsPop p) : Inv p 0 0 := by
  refine ⟨by simp, fun i => Nat.zero_le _, fun k => ?_⟩
  unfold Dn
  simp only [Pi.zero_apply, Nat.sub_zero, zero_add]
  have : ((∑ i, fl p k i : ℕ) : ℝ) ≤ k := by
    push_cast
    calc ∑ i, (fl p k i : ℝ) ≤ ∑ i, (p i : ℝ) * k / totalPop p :=
          Finset.sum_le_sum (fun i _ => fl_le hp k i)
      _ = k := sum_q hp k
  exact_mod_cast this

lemma Inv.lower {T : ℕ} {y : Fin n → ℕ} (h : Inv p T y) (i : Fin n) : fl p T i ≤ y i := by
  have h0 := h.2.2 0
  unfold Dn at h0
  have : ∑ j, (fl p (T + 0) j - y j) = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at this
  have := this i (mem_univ i)
  simp at this; omega

lemma Inv.qc {T : ℕ} {y : Fin n → ℕ} (h : Inv p T y) (i : Fin n) :
    y i = fl p T i ∨ y i = cl p T i := by
  have h1 := h.lower i
  have h2 := h.2.1 i
  have h3 := cl_le_fl_add_one (p := p) T i
  omega

lemma Inv_step (hp : IsPop p) {T : ℕ} {y : Fin n → ℕ} (h : Inv p T y) (i : Fin n)
    (hL : i ∈ calL p T (fun j => (y j : ℝ))) (hU : i ∈ calU p T (fun j => (y j : ℝ))) :
    Inv p (T + 1) (y + Pi.single i 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Pi.add_apply]; rw [Finset.sum_add_distrib, h.1]; simp
  · intro j
    by_cases hj : j = i
    · subst hj
      simp only [calU, mem_filter, mem_univ, true_and] at hU
      have : y j < cl p (T + 1) j := by
        unfold cl; rw [Nat.lt_ceil]; push_cast; exact hU
      simp; omega
    · have := h.2.1 j
      have := cl_mono hp (show T ≤ T + 1 by omega) j
      simp only [Pi.add_apply, Pi.single_apply, hj, if_false, add_zero]; omega
  · intro k
    have hk := h.2.2 (k + 1)
    have hrw : T + 1 + k = T + (k + 1) := by omega
    -- pointwise decomposition
    have hpt : ∀ j, (fl p (T + 1 + k) j - (y + Pi.single i 1 : Fin n → ℕ) j) +
        (if j = i ∧ y i < fl p (T + (k + 1)) i then 1 else 0) = fl p (T + (k + 1)) j - y j := by
      intro j
      rw [hrw]
      by_cases hj : j = i
      · subst hj; simp; split_ifs <;> omega
      · simp [hj]
    have hsum : Dn p (T + 1) (y + Pi.single i 1) k +
        (if y i < fl p (T + (k + 1)) i then 1 else 0) = Dn p T y (k + 1) := by
      unfold Dn
      rw [← Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      split_ifs with hc
      · symm; rw [Finset.card_eq_one]; exact ⟨i, by ext j; simp [hc]⟩
      · symm; rw [Finset.card_eq_zero]; ext j; simp [hc]
    by_cases hle : Dn p T y (k + 1) ≤ k
    · omega
    · have heq : Dn p T y (k + 1) = k + 1 := by omega
      have hks : kStar p T (fun j => (y j : ℝ)) ≤ k + 1 := by
        apply kStar_le _ _ _ (by omega)
        rw [S_sum_eq, heq]
      have hyi : y i < fl p (T + (k + 1)) i := by
        simp only [calL, mem_filter, mem_univ, true_and] at hL
        rw [lq_eq] at hL
        have := fl_mono hp (show T + kStar p T (fun j => (y j : ℝ)) ≤ T + (k + 1) by omega) i
        have : (y i : ℝ) < fl p (T + (k + 1)) i := lt_of_lt_of_le hL (by exact_mod_cast this)
        exact_mod_cast this
      rw [if_pos hyi] at hsum
      omega


/-! ### Extensions and good sequences -/

noncomputable def nxt (p : Fin n → ℕ) (T : ℕ) (y : Fin n → ℕ) : Fin n → ℕ :=
  if h : ∃ i, i ∈ calL p T (fun j => (y j : ℝ)) ∩ calU p T (fun j => (y j : ℝ)) then
    y + Pi.single h.choose 1 else y

lemma Inv_nxt (hp : IsPop p) {T : ℕ} {y : Fin n → ℕ} (h : Inv p T y) :
    Inv p (T + 1) (nxt p T y) ∧ y ≤ nxt p T y := by
  have hne := LU_nonempty hp T (fun j => (y j : ℝ)) h.sum_le
  unfold nxt
  rw [dif_pos hne]
  have hc := hne.choose_spec
  rw [Finset.mem_inter] at hc
  refine ⟨Inv_step hp h _ hc.1 hc.2, ?_⟩
  intro j; simp

noncomputable def extSeq (p : Fin n → ℕ) (T0 : ℕ) (y0 : Fin n → ℕ) : ℕ → Fin n → ℕ
  | 0 => y0
  | m + 1 => nxt p (T0 + m) (extSeq p T0 y0 m)

lemma extSeq_inv (hp : IsPop p) {T0 : ℕ} {y0 : Fin n → ℕ} (h : Inv p T0 y0) :
    ∀ m, Inv p (T0 + m) (extSeq p T0 y0 m) ∧ extSeq p T0 y0 m ≤ extSeq p T0 y0 (m + 1) := by
  intro m
  induction m with
  | zero =>
    have := Inv_nxt hp h
    exact ⟨by simpa [extSeq] using h, this.2⟩
  | succ m ih =>
    have h1 := (Inv_nxt hp ih.1).1
    exact ⟨h1, (Inv_nxt hp h1).2⟩

def GoodSeq (p : Fin n → ℕ) (s : ℕ → Fin n → ℕ) : Prop := ∀ h, Inv p h (s h) ∧ s h ≤ s (h + 1)

lemma goodSeq_extend (hp : IsPop p) (T0 : ℕ) (s0 : ℕ → Fin n → ℕ)
    (hinv : ∀ h ≤ T0, Inv p h (s0 h)) (hmono : ∀ h < T0, s0 h ≤ s0 (h + 1)) :
    ∃ s, GoodSeq p s ∧ ∀ h ≤ T0, s h = s0 h := by
  refine ⟨fun h => if h ≤ T0 then s0 h else extSeq p T0 (s0 T0) (h - T0), ?_, ?_⟩
  · have he := extSeq_inv hp (hinv T0 le_rfl)
    intro h
    by_cases h1 : h + 1 ≤ T0
    · simp only [if_pos h1, if_pos (show h ≤ T0 by omega)]
      exact ⟨hinv h (by omega), hmono h (by omega)⟩
    · by_cases h2 : h = T0
      · subst h2
        simp only [le_refl, if_true, if_neg h1, Nat.add_sub_cancel_left]
        refine ⟨hinv _ le_rfl, ?_⟩
        have := (he 0).2
        simpa [extSeq] using this
      · simp only [if_neg h1, if_neg (show ¬ h ≤ T0 by omega)]
        have := he (h - T0)
        rw [show T0 + (h - T0) = h by omega] at this
        refine ⟨this.1, ?_⟩
        rw [show h + 1 - T0 = h - T0 + 1 by omega]
        exact this.2
  · intro h hh; simp [hh]

lemma goodSeq_exists (hp : IsPop p) : ∃ s, GoodSeq p s := by
  obtain ⟨s, hs, _⟩ := goodSeq_extend hp 0 (fun _ => 0)
    (fun h hh => by
      have : h = 0 := by omega
      subst this; exact Inv_zero hp)
    (fun h hh => by omega)
  exact ⟨s, hs⟩

lemma GoodSeq.mono {s : ℕ → Fin n → ℕ} (hs : GoodSeq p s) {a b : ℕ} (hab : a ≤ b) : s a ≤ s b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (hs b).2

lemma GoodSeq.zero {s : ℕ → Fin n → ℕ} (hs : GoodSeq p s) : s 0 = 0 := by
  have := (hs 0).1.1
  funext i
  rw [Finset.sum_eq_zero_iff] at this
  exact this i (mem_univ i)

/-! ### From sequences to points of `K` -/

noncomputable def zOf (s : ℕ → Fin n → ℕ) (L : ℕ) : Fin n → Fin L → ℝ :=
  fun i t => (s (t.val + 1) i : ℝ) - s t.val i

lemma A_zOf (s : ℕ → Fin n → ℕ) (hs0 : s 0 = 0) (L T : ℕ) :
    A (zOf s L) T = fun i => (s (min T L) i : ℝ) := by
  induction T with
  | zero => rw [A_zero]; funext i; simp [hs0]
  | succ T ih =>
    funext i
    rw [A_succ, ih]
    unfold xe zOf
    by_cases hT : T < L
    · rw [dif_pos hT, show min (T + 1) L = T + 1 by omega, show min T L = T by omega]; ring
    · rw [dif_neg hT, show min (T + 1) L = L by omega, show min T L = L by omega]; ring

lemma K_bounds {L : ℕ} {x : Fin n → Fin L → ℝ} (hx : x ∈ K p L) (i : Fin n) (t : Fin L) :
    0 ≤ x i t ∧ x i t ≤ 1 := by
  refine ⟨hx.2.2.2 i t, ?_⟩
  rw [← hx.1 t]
  exact Finset.single_le_sum (f := fun j => x j t) (fun j _ => hx.2.2.2 j t) (mem_univ i)

lemma mem_calE_of_01 {L : ℕ} {x : Fin n → Fin L → ℝ} (hx : x ∈ K p L)
    (h01 : ∀ i t, x i t = 0 ∨ x i t = 1) : x ∈ calE p L := by
  unfold calE
  rw [mem_extremePoints]
  refine ⟨hx, ?_⟩
  intro x1 hx1 x2 hx2 hseg
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have key : ∀ i t, x1 i t = x i t ∧ x2 i t = x i t := by
    intro i t
    have hc : a * x1 i t + b * x2 i t = x i t := by
      have := congrFun (congrFun he i) t
      simpa using this
    obtain ⟨h10, h11⟩ := K_bounds hx1 i t
    obtain ⟨h20, h21⟩ := K_bounds hx2 i t
    rcases h01 i t with h | h <;> rw [h] at hc ⊢
    · constructor <;> nlinarith [mul_nonneg ha.le h10, mul_nonneg hb.le h20]
    · constructor <;> nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h11), mul_nonneg hb.le (sub_nonneg.mpr h21)]
  exact ⟨funext fun i => funext fun t => (key i t).1, funext fun i => funext fun t => (key i t).2⟩

lemma zOf_mem_K (hp : IsPop p) {s : ℕ → Fin n → ℕ} (hs : GoodSeq p s) (L : ℕ) :
    zOf s L ∈ K p L := by
  have hA := A_zOf s hs.zero L
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    unfold zOf
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ i, (s (t.val + 1) i : ℝ) = ((t.val + 1 : ℕ) : ℝ) := by
      have := (hs (t.val + 1)).1.1; exact_mod_cast this
    have h2 : ∑ i, (s t.val i : ℝ) = (t.val : ℝ) := by
      have := (hs t.val).1.1; exact_mod_cast this
    rw [h1, h2]; push_cast; ring
  · intro i t
    rw [prefix_eq_A, hA, K_floor_eq, show min (t.val + 1) L = t.val + 1 by omega]
    show ((fl p (t.val + 1) i : ℕ) : ℝ) ≤ (s (t.val + 1) i : ℝ)
    exact_mod_cast (hs (t.val + 1)).1.lower i
  · intro i t
    rw [prefix_eq_A, hA, K_ceil_eq, show min (t.val + 1) L = t.val + 1 by omega]
    show (s (t.val + 1) i : ℝ) ≤ ((cl p (t.val + 1) i : ℕ) : ℝ)
    exact_mod_cast (hs (t.val + 1)).1.2.1 i
  · intro i t
    unfold zOf
    have := (hs t.val).2 i
    rw [sub_nonneg]; exact_mod_cast this

lemma zOf_mem_E (hp : IsPop p) {s : ℕ → Fin n → ℕ} (hs : GoodSeq p s) (L : ℕ) :
    zOf s L ∈ calE p L := by
  apply mem_calE_of_01 (zOf_mem_K hp hs L)
  intro i t
  have hb := K_bounds (zOf_mem_K hp hs L) i t
  unfold zOf at hb ⊢
  have hm := (hs t.val).2 i
  rw [← Nat.cast_sub hm] at hb ⊢
  have : s (t.val + 1) i - s t.val i ≤ 1 := by exact_mod_cast hb.2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> simp

/-! ### Solutions from good sequences -/

noncomputable def mkSol (p0 : Fin n → ℕ) (s0 : ℕ → Fin n → ℕ) : Solution :=
  fun {m} q h => (Classical.epsilon (fun s : ℕ → Fin m → ℕ => (IsPop q → GoodSeq q s) ∧
    ∀ e : n = m, cast (congrArg (fun k => Fin k → ℕ) e) p0 = q →
      cast (congrArg (fun k => ℕ → Fin k → ℕ) e) s0 = s)) h

lemma mkSol_spec {p0 : Fin n → ℕ} {s0 : ℕ → Fin n → ℕ} (hg : GoodSeq p0 s0) {m : ℕ}
    (q : Fin m → ℕ) :
    (IsPop q → GoodSeq q (fun h => mkSol p0 s0 q h)) ∧
    ∀ e : n = m, cast (congrArg (fun k => Fin k → ℕ) e) p0 = q →
      cast (congrArg (fun k => ℕ → Fin k → ℕ) e) s0 = (fun h => mkSol p0 s0 q h) := by
  have hex : ∃ s : ℕ → Fin m → ℕ, (IsPop q → GoodSeq q s) ∧
      ∀ e : n = m, cast (congrArg (fun k => Fin k → ℕ) e) p0 = q →
        cast (congrArg (fun k => ℕ → Fin k → ℕ) e) s0 = s := by
    by_cases hq : ∃ e : n = m, cast (congrArg (fun k => Fin k → ℕ) e) p0 = q
    · obtain ⟨e, he⟩ := hq
      subst e
      simp only [cast_eq] at he
      subst he
      exact ⟨s0, fun _ => hg, fun e _ => by simp⟩
    · by_cases hpq : IsPop q
      · obtain ⟨s, hs⟩ := goodSeq_exists hpq
        exact ⟨s, fun _ => hs, fun e he => absurd ⟨e, he⟩ hq⟩
      · exact ⟨fun _ => 0, fun h => absurd h hpq, fun e he => absurd ⟨e, he⟩ hq⟩
  exact Classical.epsilon_spec hex

lemma mkSol_at {p0 : Fin n → ℕ} {s0 : ℕ → Fin n → ℕ} (hg : GoodSeq p0 s0) (h : ℕ) :
    mkSol p0 s0 p0 h = s0 h := by
  have := (mkSol_spec hg p0).2 rfl rfl
  exact (congrFun this h).symm

lemma mkSol_good {p0 : Fin n → ℕ} {s0 : ℕ → Fin n → ℕ} (hg : GoodSeq p0 s0) :
    IsSolution (mkSol p0 s0) ∧ HouseMonotone (mkSol p0 s0) ∧ QuotaCompliant (mkSol p0 s0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m q H hq _
    exact (((mkSol_spec hg q).1 hq) H).1.1
  · intro m q hq H₁ H₂ H₃ _ h12 h23
    have hs := (mkSol_spec hg q).1 hq
    exact ⟨hs.mono h12.le, hs.mono h23.le⟩
  · intro m q H hq _ i
    have hs := (mkSol_spec hg q).1 hq
    rw [quota_floor, quota_ceil]
    exact (hs H).1.qc i

lemma mem_calA_of_good {p0 : Fin n → ℕ} {s0 : ℕ → Fin n → ℕ} (hg : GoodSeq p0 s0) (H : ℕ) :
    s0 H ∈ calA p0 H :=
  ⟨mkSol p0 s0, (mkSol_good hg).1, (mkSol_good hg).2.1, (mkSol_good hg).2.2, mkSol_at hg H⟩


/-! ### Sums of columns -/

lemma xe_nonneg {L : ℕ} {x : Fin n → Fin L → ℝ} (hx : x ∈ K p L) (j : Fin n) (m : ℕ) :
    0 ≤ xe x j m := by
  unfold xe; split_ifs
  · exact hx.2.2.2 _ _
  · exact le_rfl

lemma sum_xe_le {L : ℕ} {x : Fin n → Fin L → ℝ} (hx : x ∈ K p L) (m : ℕ) :
    ∑ j, xe x j m ≤ 1 := by
  unfold xe
  by_cases hm : m < L
  · simp only [dif_pos hm]; rw [hx.1]
  · simp [dif_neg hm]

lemma sum_A_le {L : ℕ} {x : Fin n → Fin L → ℝ} (hx : x ∈ K p L) (T : ℕ) :
    ∑ j, A x T j ≤ T := by
  simp only [A_eq_range]
  rw [Finset.sum_comm]
  calc ∑ m ∈ range T, ∑ j, xe x j m ≤ ∑ m ∈ range T, (1 : ℝ) :=
        Finset.sum_le_sum (fun m _ => sum_xe_le hx m)
    _ = T := by simp

/-! ### The seat structure of points of `K` -/

lemma seat_in_U {L : ℕ} {x : Fin n → Fin L → ℝ} (hx : x ∈ K p L) (t : Fin L) (i : Fin n)
    (y : ℕ) (hy : A x t.val i = y) (hxi : x i t = 1) : i ∈ calU p t.val (A x t.val) := by
  simp only [calU, mem_filter, mem_univ, true_and]
  by_contra hc
  rw [not_lt, hy] at hc
  have h3 := hx.2.2.1 i t
  rw [prefix_eq_A, K_ceil_eq, A_succ, hy, xe_of_lt, hxi] at h3
  have : cl p (t.val + 1) i ≤ y := by
    unfold cl; rw [Nat.ceil_le]; push_cast; exact hc
  have : ((cl p (t.val + 1) i : ℕ) : ℝ) ≤ y := by exact_mod_cast this
  linarith

lemma seat_in_L (hp : IsPop p) {L : ℕ} {x : Fin n → Fin L → ℝ} (hx : x ∈ K p L) (t : Fin L)
    (i : Fin n) (hxi : 0 < x i t) (hlook : t.val + tau p t.val (A x t.val) ≤ L) :
    i ∈ calL p t.val (A x t.val) := by
  set T := t.val with hT
  set y := A x T with hy
  have hsum : ∑ j, y j ≤ T := sum_A_le hx T
  obtain ⟨hk1, hk⟩ := kStar_mem hp T y hsum
  set k := kStar p T y with hkdef
  by_contra hi
  rw [calL_eq] at hi
  by_cases hS : S p T y k = univ
  · exact hi (hS ▸ mem_univ i)
  have htau : tau p T y = k := by unfold tau; rw [if_neg hS]
  rw [htau] at hlook
  -- lower quota at seat T + k
  have hlow : ∀ j, (lq p T k j : ℝ) ≤ A x (T + k) j := by
    intro j
    have h2 := hx.2.1 j ⟨T + k - 1, by omega⟩
    rw [prefix_eq_A, K_floor_eq] at h2
    simp only at h2
    rw [show T + k - 1 + 1 = T + k by omega] at h2
    rw [lq_eq]; exact h2
  have hdiff : ∀ j, A x (T + k) j - A x T j = ∑ m ∈ range k, xe x j (T + m) := by
    intro j; rw [A_eq_range, A_eq_range, Finset.sum_range_add]; ring
  have h1 : ∑ j ∈ S p T y k, ((lq p T k j : ℝ) - y j) ≤
      ∑ m ∈ range k, ∑ j ∈ S p T y k, xe x j (T + m) := by
    calc ∑ j ∈ S p T y k, ((lq p T k j : ℝ) - y j)
        ≤ ∑ j ∈ S p T y k, (A x (T + k) j - A x T j) :=
          Finset.sum_le_sum (fun j _ => by rw [hy]; linarith [hlow j])
      _ = ∑ j ∈ S p T y k, ∑ m ∈ range k, xe x j (T + m) :=
          Finset.sum_congr rfl (fun j _ => hdiff j)
      _ = _ := Finset.sum_comm
  have hg0 : ∑ j ∈ S p T y k, xe x j (T + 0) ≤ 1 - x i t := by
    have hsub : insert i (S p T y k) ⊆ univ := subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun j => xe x j (T + 0))
      (fun j _ _ => xe_nonneg hx j _)
    rw [Finset.sum_insert hi] at this
    have h1' := sum_xe_le hx (T + 0)
    have : xe x i (T + 0) = x i t := by rw [add_zero, hT, xe_of_lt]
    linarith
  have hg : ∀ m, ∑ j ∈ S p T y k, xe x j (T + m) ≤ 1 := by
    intro m
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun j _ _ => xe_nonneg hx j _)) (sum_xe_le hx _)
  have h2 : ∑ m ∈ range k, ∑ j ∈ S p T y k, xe x j (T + m) ≤ (k : ℝ) - x i t := by
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', Finset.sum_range_succ']
    have : ∑ m ∈ range k', ∑ j ∈ S p T y (k' + 1), xe x j (T + (m + 1)) ≤ k' := by
      calc _ ≤ ∑ m ∈ range k', (1 : ℝ) := Finset.sum_le_sum (fun m _ => by rw [← hk']; exact hg _)
        _ = k' := by simp
    rw [← hk'] at this ⊢
    have hg0' := hg0
    push_cast [hk'] at this ⊢
    rw [hk'] at hg0'
    linarith
  linarith

/-! ### `Φ` -/

lemma Phi_one_pos (hp : IsPop p) : 1 ≤ Phi p 1 := by
  have hne : {k : ℕ | 1 ≤ k ∧ k ≤ ∑ i, ⌊(p i : ℝ) * k / totalPop p⌋₊}.Nonempty := by
    refine ⟨totalPop p, P_pos' hp, ?_⟩
    have : ∀ i, ⌊(p i : ℝ) * (totalPop p : ℕ) / totalPop p⌋₊ = p i := by
      intro i; rw [mul_div_assoc, div_self (P_pos hp).ne', mul_one, Nat.floor_natCast]
    simp only [this]; exact le_rfl
  exact (Nat.sInf_mem hne).1

lemma calE_nonempty (hp : IsPop p) (L : ℕ) : (calE p L).Nonempty := by
  obtain ⟨s, hs⟩ := goodSeq_exists hp
  exact ⟨_, zOf_mem_E hp hs L⟩

lemma Phi_succ_succ (H : ℕ) : Phi p (H + 2) = sSup {v : ℕ | ∃ T : ℕ, 1 ≤ T ∧ T ≤ H + 1 ∧
      ∃ x ∈ calE p (Phi p (H + 1)), v = T + tau p T (A x T)} := by
  rw [Phi]

lemma Phi_bdd (hp : IsPop p) (H : ℕ) : BddAbove {v : ℕ | ∃ T : ℕ, 1 ≤ T ∧ T ≤ H + 1 ∧
      ∃ x ∈ calE p (Phi p (H + 1)), v = T + tau p T (A x T)} := by
  refine ⟨H + 1 + (H + 2) * totalPop p + 1, ?_⟩
  rintro v ⟨T, hT1, hT2, x, hx, rfl⟩
  have hxK : x ∈ K p (Phi p (H + 1)) := hx.1
  have := tau_le hp T (A x T) (sum_A_le hxK T)
  have hk0 : k0 p T ≤ (H + 2) * totalPop p := by
    unfold k0
    have : (T + 1) * totalPop p ≤ (H + 2) * totalPop p := Nat.mul_le_mul_right _ (by omega)
    omega
  omega

lemma le_Phi (hp : IsPop p) (H T : ℕ) (hT1 : 1 ≤ T) (hT2 : T ≤ H + 1)
    (x : Fin n → Fin (Phi p (H + 1)) → ℝ) (hx : x ∈ calE p (Phi p (H + 1))) :
    T + tau p T (A x T) ≤ Phi p (H + 2) := by
  rw [Phi_succ_succ]
  exact le_csSup (Phi_bdd hp H) ⟨T, hT1, hT2, x, hx, rfl⟩

lemma Phi_ge (hp : IsPop p) : ∀ H, 1 ≤ H → H ≤ Phi p H := by
  intro H hH
  induction H using Nat.strong_induction_on with
  | _ H ih =>
    match H, hH with
    | 1, _ => exact Phi_one_pos hp
    | H' + 2, _ =>
      obtain ⟨x, hx⟩ := calE_nonempty hp (Phi p (H' + 1))
      have := le_Phi hp H' (H' + 1) (by omega) le_rfl x hx
      have := tau_pos hp (H' + 1) (A x (H' + 1)) (sum_A_le hx.1 _)
      omega


/-! ### Integral points -/

lemma int_01 {L : ℕ} {x : Fin n → Fin L → ℝ} (hx : x ∈ K p L) (i : Fin n) (t : Fin L)
    (h : ∃ z : ℤ, x i t = z) : x i t = 0 ∨ x i t = 1 := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨h0, h1⟩ := K_bounds hx i t
  rw [hz] at h0 h1 ⊢
  have : (0 : ℤ) ≤ z := by exact_mod_cast h0
  have : z ≤ (1 : ℤ) := by exact_mod_cast h1
  have : z = 0 ∨ z = 1 := by omega
  rcases this with rfl | rfl <;> simp

noncomputable def xn {L : ℕ} (x : Fin n → Fin L → ℝ) (i : Fin n) (m : ℕ) : ℕ :=
  if xe x i m = 1 then 1 else 0

noncomputable def yv {L : ℕ} (x : Fin n → Fin L → ℝ) (h : ℕ) : Fin n → ℕ :=
  fun i => ∑ m ∈ range h, xn x i m

lemma xe_xn {L : ℕ} {x : Fin n → Fin L → ℝ} (h01 : ∀ i t, x i t = 0 ∨ x i t = 1)
    (i : Fin n) (m : ℕ) : xe x i m = (xn x i m : ℝ) := by
  unfold xn
  split_ifs with h
  · rw [h]; simp
  · unfold xe at h ⊢
    split_ifs with hm
    · rw [dif_pos hm] at h; rcases h01 i ⟨m, hm⟩ with h' | h'
      · rw [h']; simp
      · exact absurd h' h
    · simp

lemma A_yv {L : ℕ} {x : Fin n → Fin L → ℝ} (h01 : ∀ i t, x i t = 0 ∨ x i t = 1) (h : ℕ) :
    A x h = fun i => (yv x h i : ℝ) := by
  funext i; rw [A_eq_range]; unfold yv; push_cast
  exact Finset.sum_congr rfl (fun m _ => xe_xn h01 i m)

lemma yv_succ {L : ℕ} (x : Fin n → Fin L → ℝ) (h : ℕ) (i : Fin n) :
    yv x (h + 1) i = yv x h i + xn x i h := by
  unfold yv; rw [Finset.sum_range_succ]

lemma yv_mono {L : ℕ} (x : Fin n → Fin L → ℝ) (h : ℕ) : yv x h ≤ yv x (h + 1) := by
  intro i; show yv x h i ≤ yv x (h + 1) i; rw [yv_succ]; omega

lemma S_univ_zero (hp : IsPop p) :
    S p 0 (0 : Fin n → ℝ) (kStar p 0 (0 : Fin n → ℝ)) = univ := by
  have hsum : ∑ j, (0 : Fin n → ℝ) j ≤ ((0 : ℕ) : ℝ) := by simp
  obtain ⟨hk1, hk⟩ := kStar_mem hp 0 (0 : Fin n → ℝ) hsum
  set k := kStar p 0 (0 : Fin n → ℝ)
  by_contra hne
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 ∉ S p 0 (0 : Fin n → ℝ) k := by
    by_contra hc; push Not at hc; exact hne (eq_univ_of_forall hc)
  simp only [S, mem_filter, mem_univ, true_and, not_lt, Pi.zero_apply] at hj0
  have hP := P_pos hp
  have hle : ∀ j, (lq p 0 k j : ℝ) ≤ (p j : ℝ) * k / totalPop p := by
    intro j; unfold lq; simp only [Nat.cast_zero, zero_add]
    exact Nat.floor_le (div_nonneg (by positivity) hP.le)
  have hlt : (lq p 0 k j0 : ℝ) < (p j0 : ℝ) * k / totalPop p := by
    have h1 : (lq p 0 k j0 : ℝ) ≤ 0 := hj0
    have : (0 : ℝ) < (p j0 : ℝ) * k / totalPop p := by
      apply div_pos _ hP
      have : (0 : ℝ) < p j0 := by exact_mod_cast hp.2 j0
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      positivity
    linarith
  have hsum1 : ∑ j ∈ S p 0 (0 : Fin n → ℝ) k, ((lq p 0 k j : ℝ) - (0 : Fin n → ℝ) j) ≤
      ∑ j, (lq p 0 k j : ℝ) := by
    simp only [Pi.zero_apply, sub_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => by positivity)
  have hsum2 : ∑ j, (lq p 0 k j : ℝ) < ∑ j, (p j : ℝ) * k / totalPop p :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨j0, mem_univ _, hlt⟩
  rw [sum_q hp] at hsum2
  linarith

lemma tau_zero (hp : IsPop p) : tau p 0 (0 : Fin n → ℝ) = 1 := by
  unfold tau; rw [if_pos (S_univ_zero hp)]

/-- One step of the inner induction behind Lemma 5. -/
lemma col_step (hp : IsPop p) {H : ℕ} (hH : 0 < H) {x : Fin n → Fin (Phi p H) → ℝ}
    (hx : x ∈ calE p (Phi p H)) (h01 : ∀ i t, x i t = 0 ∨ x i t = 1) (T : ℕ) (hT : T + 1 ≤ H)
    (hinv : ∀ h ≤ T, Inv p h (yv x h)) :
    (∀ t : Fin (Phi p H), t.val = T → ∃ i0 ∈ calL p T (A x T) ∩ calU p T (A x T),
      ∀ j, x j t = if j = i0 then 1 else 0) ∧ Inv p (T + 1) (yv x (T + 1)) := by
  have hL : H ≤ Phi p H := Phi_ge hp H hH
  have hxK : x ∈ K p (Phi p H) := hx.1
  set t : Fin (Phi p H) := ⟨T, by omega⟩ with ht
  -- the seat `T + 1` goes to a unique state
  obtain ⟨i0, hi0⟩ : ∃ i0, x i0 t = 1 := by
    by_contra hc
    push Not at hc
    have : ∑ j, x j t = 0 := Finset.sum_eq_zero (fun j _ => (h01 j t).resolve_right (hc j))
    rw [hxK.1 t] at this; norm_num at this
  have hcol : ∀ j, x j t = if j = i0 then 1 else 0 := by
    intro j
    split_ifs with hj
    · rw [hj, hi0]
    · have hpair := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ {i0, j})
        (f := fun j => x j t) (fun j _ _ => hxK.2.2.2 j t)
      rw [Finset.sum_pair (Ne.symm hj), hxK.1 t, hi0] at hpair
      rcases h01 j t with h | h
      · exact h
      · rw [h] at hpair; norm_num at hpair
  -- the lookahead
  have hlook : T + tau p T (A x T) ≤ Phi p H := by
    rcases Nat.eq_zero_or_pos T with hT0 | hT0
    · subst hT0
      rw [A_zero, tau_zero hp]; omega
    · obtain ⟨H', rfl⟩ : ∃ H', H = H' + 2 := ⟨H - 2, by omega⟩
      obtain ⟨s, hs, hsT⟩ := goodSeq_extend hp T (yv x) hinv (fun h _ => yv_mono x h)
      have hL' : H' + 1 ≤ Phi p (H' + 1) := Phi_ge hp (H' + 1) (by omega)
      have hx' := zOf_mem_E hp hs (Phi p (H' + 1))
      have hA' : A (zOf s (Phi p (H' + 1))) T = A x T := by
        rw [A_zOf s hs.zero, A_yv h01, show min T (Phi p (H' + 1)) = T by omega, hsT T le_rfl]
      have := le_Phi hp H' T hT0 (by omega) _ hx'
      rw [hA'] at this
      exact this
  have hU := seat_in_U hxK t i0 (yv x T i0) (by rw [A_yv h01]) hi0
  have hLm := seat_in_L hp hxK t i0 (by rw [hi0]; norm_num) hlook
  refine ⟨fun t' ht' => ?_, ?_⟩
  · have : t' = t := Fin.ext ht'
    subst this
    exact ⟨i0, Finset.mem_inter.mpr ⟨hLm, hU⟩, hcol⟩
  · have hy : yv x (T + 1) = yv x T + Pi.single i0 1 := by
      funext j
      rw [yv_succ]
      have : xn x j T = if j = i0 then 1 else 0 := by
        unfold xn
        rw [show xe x j T = x j t from xe_of_lt x j t, hcol j]
        split_ifs <;> simp_all
      rw [this]
      by_cases hj : j = i0
      · subst hj; simp
      · simp [hj]
    rw [hy]
    rw [A_yv h01] at hLm hU
    exact Inv_step hp (hinv T le_rfl) i0 hLm hU

lemma chain (hp : IsPop p) {H : ℕ} (hH : 0 < H) {x : Fin n → Fin (Phi p H) → ℝ}
    (hx : x ∈ calE p (Phi p H)) (h01 : ∀ i t, x i t = 0 ∨ x i t = 1) :
    ∀ T, T ≤ H → ∀ h ≤ T, Inv p h (yv x h) := by
  intro T
  induction T with
  | zero =>
    intro _ h hh
    have : h = 0 := by omega
    subst this
    have : yv x 0 = 0 := by funext i; simp [yv]
    rw [this]; exact Inv_zero hp
  | succ T ih =>
    intro hT h hh
    have ih' := ih (by omega)
    rcases Nat.lt_or_ge h (T + 1) with h1 | h1
    · exact ih' h (by omega)
    · have : h = T + 1 := by omega
      subst this
      exact (col_step hp hH hx h01 T hT ih').2

/-! ### Solutions give good sequences -/

lemma good_of_sol {f : Solution} (hs : IsSolution f) (hm : HouseMonotone f) (hq : QuotaCompliant f)
    (hp : IsPop p) : GoodSeq p (fun h => ext f p h) := by
  have hext0 : ext f p 0 = 0 := by simp [MonoApport.Flow.ext]
  have hextp : ∀ h, 0 < h → ext f p h = f p h := fun h hh => by
    simp [MonoApport.Flow.ext, hh.ne']
  have hsum : ∀ h, ∑ i, ext f p h i = h := by
    intro h
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp [hext0]
    · rw [hextp h hh]; exact hs n p h hp hh
  have hqc : ∀ h i, fl p h i ≤ ext f p h i ∧ ext f p h i ≤ cl p h i := by
    intro h i
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp [hext0, fl]
    · rw [hextp h hh]
      have hq1 : f p h i = fl p h i ∨ f p h i = cl p h i := hq n p h hp hh i
      have := fl_le_cl (p := p) h i
      rcases hq1 with h1 | h1 <;> omega
  have hmono : ∀ h, ext f p h ≤ ext f p (h + 1) := by
    intro h
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · rw [hext0]; exact fun i => Nat.zero_le _
    · rw [hextp h hh, hextp (h + 1) (by omega)]
      exact (hm n p hp h (h + 1) (h + 2) hh (by omega) (by omega)).1
  have hmono' : ∀ a b, a ≤ b → ext f p a ≤ ext f p b := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact ih.trans (hmono b)
  intro h
  show Inv p h (ext f p h) ∧ ext f p h ≤ ext f p (h + 1)
  refine ⟨⟨hsum h, fun i => (hqc h i).2, fun k => ?_⟩, hmono h⟩
  unfold Dn
  have hle : ∀ i, fl p (h + k) i - ext f p h i ≤ ext f p (h + k) i - ext f p h i :=
    fun i => Nat.sub_le_sub_right (hqc (h + k) i).1 _
  have h2 : ∑ i, (ext f p (h + k) i - ext f p h i) + ∑ i, ext f p h i = ∑ i, ext f p (h + k) i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hmono' h (h + k) (by omega) i))
  have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => hle i)
  rw [hsum, hsum] at h2
  omega


lemma zOf_01 (hp : IsPop p) {s : ℕ → Fin n → ℕ} (hs : GoodSeq p s) (L : ℕ) :
    ∀ i t, zOf s L i t = 0 ∨ zOf s L i t = 1 := by
  intro i t
  have hb := K_bounds (zOf_mem_K hp hs L) i t
  unfold zOf at hb ⊢
  have hm := (hs t.val).2 i
  rw [← Nat.cast_sub hm] at hb ⊢
  have : s (t.val + 1) i - s t.val i ≤ 1 := by exact_mod_cast hb.2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> simp

lemma col_single {L : ℕ} {x : Fin n → Fin L → ℝ} (hxK : x ∈ K p L)
    (h01 : ∀ i t, x i t = 0 ∨ x i t = 1) (t : Fin L) :
    ∃ i0, x i0 t = 1 ∧ ∀ j, x j t = if j = i0 then 1 else 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i0, x i0 t = 1 := by
    by_contra hc
    push Not at hc
    have : ∑ j, x j t = 0 := Finset.sum_eq_zero (fun j _ => (h01 j t).resolve_right (hc j))
    rw [hxK.1 t] at this; norm_num at this
  refine ⟨i0, hi0, fun j => ?_⟩
  split_ifs with hj
  · rw [hj, hi0]
  · have hpair := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ {i0, j})
      (f := fun j => x j t) (fun j _ _ => hxK.2.2.2 j t)
    rw [Finset.sum_pair (Ne.symm hj), hxK.1 t, hi0] at hpair
    rcases h01 j t with h | h
    · exact h
    · rw [h] at hpair; norm_num at hpair

end MonoAux


open MonoApport.Flow MonoAux Finset

theorem solution {n : ℕ} (p : Fin n → ℕ) (hp : IsPop p) (H : ℕ) (hH : 0 < H)
    (x : Fin n → Fin (Phi p H) → ℝ) (hx : x ∈ calE p (Phi p H)) :
    ∀ T : ℕ, T + 1 ≤ H → ∀ i : Fin n, i ∉ calL p T (A x T) ∩ calU p T (A x T) →
      ∀ t : Fin (Phi p H), t.val = T → x i t = 0 := by
  intro T hT i hi t ht
  have hL : H ≤ Phi p H := Phi_ge hp H hH
  have h01 : ∀ i t, x i t = 0 ∨ x i t = 1 := fun i t =>
    int_01 hx.1 i t (MonoApport.Flow.lemma_3 p hp (Phi p H) (by omega) x hx i t)
  have hinv := chain hp hH hx h01 T (by omega)
  obtain ⟨i0, hi0, hcol⟩ := (col_step hp hH hx h01 T hT hinv).1 t ht
  rw [hcol i]
  have : i ≠ i0 := fun h => hi (h ▸ hi0)
  simp [this]
