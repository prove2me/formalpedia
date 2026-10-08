-- Prove2me | solution 1 for MinimaxRegretRL.Hoeffding.lemma18_optimism
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:33:02.259959+00:00
-- url     : https://prove2.me/submissions/a2d63923-04ac-45ea-84de-3da9f5bc24b6

import Mathlib
import Definitions.Def_MinimaxRegretRL_Hoeffding_Analysis

set_option autoImplicit false

namespace MinimaxRegretRL.Hoeffding.L18Opt

open MinimaxRegretRL.Hoeffding

lemma sup_ge {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ)
    (hf : ∀ i ∈ s, c ≤ f i) : c ≤ s.sup' hs f := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hs f
  rw [he]; exact hf i hi

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]

lemma pvf_bounds (M : MDP S A) (H : ℕ) (π : Policy S A H) :
    ∀ (fuel h : ℕ) (x : S), 0 ≤ policyValueFuel M H π fuel h x ∧
      policyValueFuel M H π fuel h x ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro h x; simp [policyValueFuel]
  | succ n ih =>
    intro h x
    simp only [policyValueFuel]
    split_ifs with hh
    · obtain ⟨hP0, hP1⟩ := M.kernel x (π x ⟨h, hh⟩)
      have hR := M.reward_mem x (π x ⟨h, hh⟩)
      constructor
      · have : 0 ≤ ∑ y : S, M.P x (π x ⟨h, hh⟩) y * policyValueFuel M H π n (h + 1) y :=
          Finset.sum_nonneg (fun y _ => mul_nonneg (hP0 y) (ih (h+1) y).1)
        linarith [hR.1]
      · have h2 : ∑ y : S, M.P x (π x ⟨h, hh⟩) y * policyValueFuel M H π n (h + 1) y ≤
            ∑ y : S, M.P x (π x ⟨h, hh⟩) y * (n:ℝ) :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih (h+1) y).2 (hP0 y))
        rw [← Finset.sum_mul, hP1] at h2
        push_cast
        linarith [hR.2]
    · simp only [le_refl, true_and]
      push_cast
      positivity

lemma opt_bounds (M : MDP S A) (H h : ℕ) (x : S) :
    0 ≤ optimalValue M H h x ∧ optimalValue M H h x ≤ ((H - h : ℕ) : ℝ) := by
  unfold optimalValue
  constructor
  · apply sup_ge
    intro π _
    exact (pvf_bounds M H π (H - h) h x).1
  · apply Finset.sup'_le
    intro π _
    exact (pvf_bounds M H π (H - h) h x).2

lemma pv_succ (M : MDP S A) (H : ℕ) (π : Policy S A H) (h : ℕ) (hh : h < H) (x : S) :
    policyValue M H π h x = M.R x (π x ⟨h, hh⟩) +
      ∑ y : S, M.P x (π x ⟨h, hh⟩) y * policyValue M H π (h + 1) y := by
  unfold policyValue
  rw [show H - h = (H - (h + 1)) + 1 by omega]
  simp only [policyValueFuel, dif_pos hh]

/-- The optimal Q-function. -/
noncomputable def Qs (M : MDP S A) (H h : ℕ) (x : S) (a : A) : ℝ :=
  M.R x a + ∑ y : S, M.P x a y * optimalValue M H (h + 1) y

lemma opt_le_of (M : MDP S A) (H h : ℕ) (hh : h < H) (x : S) (T : ℝ)
    (hT : ∀ a, Qs M H h x a ≤ T) : optimalValue M H h x ≤ T := by
  unfold optimalValue
  apply Finset.sup'_le
  intro π _
  rw [pv_succ M H π h hh x]
  refine le_trans ?_ (hT (π x ⟨h, hh⟩))
  unfold Qs
  have hP0 := (M.kernel x (π x ⟨h, hh⟩)).1
  have : ∑ y : S, M.P x (π x ⟨h, hh⟩) y * policyValue M H π (h + 1) y ≤
      ∑ y : S, M.P x (π x ⟨h, hh⟩) y * optimalValue M H (h + 1) y := by
    apply Finset.sum_le_sum
    intro y _
    apply mul_le_mul_of_nonneg_left _ (hP0 y)
    unfold optimalValue
    exact Finset.le_sup' (fun π : Policy S A H => policyValue M H π (h + 1) y) (by simp)
  linarith

lemma Qs_le_H (M : MDP S A) (H h : ℕ) (hh : h < H) (x : S) (a : A) :
    Qs M H h x a ≤ H := by
  unfold Qs
  obtain ⟨hP0, hP1⟩ := M.kernel x a
  have hR := M.reward_mem x a
  have h2 : ∑ y : S, M.P x a y * optimalValue M H (h + 1) y ≤
      ∑ y : S, M.P x a y * ((H - (h + 1) : ℕ) : ℝ) :=
    Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (opt_bounds M H (h+1) y).2 (hP0 y))
  rw [← Finset.sum_mul, hP1] at h2
  have h3 : ((H - (h + 1) : ℕ) : ℝ) = (H : ℝ) - h - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [h3] at h2
  have : (0:ℝ) ≤ h := Nat.cast_nonneg h
  linarith [hR.2]

lemma var_le (M : MDP S A) (H h : ℕ) (x : S) (a : A) :
    trueVariance M H h x a ≤ (H : ℝ) ^ 2 := by
  unfold trueVariance
  obtain ⟨hP0, hP1⟩ := M.kernel x a
  have h2 : ∑ y : S, M.P x a y * (optimalValue M H h y) ^ 2 ≤
      ∑ y : S, M.P x a y * (H : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro y _
    apply mul_le_mul_of_nonneg_left _ (hP0 y)
    obtain ⟨b0, b1⟩ := opt_bounds M H h y
    have : ((H - h : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le H h
    exact pow_le_pow_left₀ b0 (le_trans b1 this) 2
  rw [← Finset.sum_mul, hP1] at h2
  nlinarith [sq_nonneg (∑ y : S, M.P x a y * optimalValue M H h y)]

lemma c1_le_bonus (S' A' H K n : ℕ) (δ v : ℝ) (hn : 0 < n)
    (hL : 1 ≤ algorithmLog S' A' H K δ) (hv : v ≤ (H : ℝ) ^ 2) :
    c1 S' A' H K n δ v ≤ bonus S' A' H K n δ := by
  unfold c1 bonus
  set L := algorithmLog S' A' H K δ with hLdef
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  set s := Real.sqrt (n : ℝ) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hn1
  have hss : s * s = n := Real.mul_self_sqrt (by linarith)
  have hspos : 0 < s := by linarith
  have hH0 : (0:ℝ) ≤ H := Nat.cast_nonneg H
  set t := (H : ℝ) * L / s with ht
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg hH0 (by linarith)) hspos.le
  have hA : Real.sqrt (v * L / n) ≤ t := by
    rw [show t = Real.sqrt (t ^ 2) from (Real.sqrt_sq ht0).symm]
    apply Real.sqrt_le_sqrt
    rw [ht, div_pow, ← hss]
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have : v * L ≤ (H:ℝ) ^ 2 * L := mul_le_mul_of_nonneg_right hv (by linarith)
    have h2 : (H:ℝ) ^ 2 * L ≤ (H:ℝ) ^ 2 * L ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    have h3 : (s ^ 2 : ℝ) = s * s := by ring
    rw [mul_pow, h3]
    have hsq : 0 ≤ s * s := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (le_trans this h2) hsq]
  have hB : 14 * (H:ℝ) * L / (3 * n) ≤ 14 / 3 * t := by
    rw [ht, ← hss]
    have hHL : 0 ≤ (H:ℝ) * L := mul_nonneg hH0 (by linarith)
    rw [div_le_iff₀ (by positivity)]
    have : (H:ℝ) * L / s * (s * s) = H * L * s := by field_simp
    have e : 14 / 3 * (↑H * L / s) * (3 * (s * s)) = 14 * (H * L * s) := by
      rw [← this]; ring
    rw [e]
    nlinarith
  have hC : 7 * (H:ℝ) * L / s = 7 * t := by rw [ht]; ring
  rw [hC]
  linarith

variable [DecidableEq S] [DecidableEq A]

lemma value_ge (Q : ℕ → S → A → ℝ) (h : ℕ) (x : S) (a : A) : Q h x a ≤ valueAt Q h x := by
  unfold valueAt
  exact Finset.le_sup' (fun a : A => Q h x a) (Finset.mem_univ a)

lemma step (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ)
    (hprev : ∀ h, h < H → ∀ x a, Qs M H h x a ≤ prevQ h x a)
    (hconf : ∀ h, h < H → ∀ x a, 0 < countSA hist x a →
      -(bonus (Fintype.card S) (Fintype.card A) H K (countSA hist x a) δ) ≤
        ∑ y : S, (empirical hist x a y - M.P x a y) * optimalValue M H (h + 1) y)
    (h : ℕ) (hh : h < H)
    (hnext : ∀ y, optimalValue M H (h + 1) y ≤ valueAt (qAt M H K δ hist prevQ) (h + 1) y)
    (x : S) (a : A) : Qs M H h x a ≤ qAt M H K δ hist prevQ h x a := by
  have hnext' := hnext
  unfold qAt
  unfold qAt at hnext'
  rw [show H - h = (H - (h + 1)) + 1 by omega]
  simp only [qFuel, if_pos hh]
  split_ifs with hc
  · exact Qs_le_H M H h hh x a
  · have hpos : 0 < countSA hist x a := Nat.pos_of_ne_zero hc
    refine le_min (hprev h hh x a) (le_min (Qs_le_H M H h hh x a) ?_)
    have he0 : ∀ y, 0 ≤ empirical hist x a y := fun y => by
      unfold empirical; positivity
    have h1 : ∑ y : S, empirical hist x a y * optimalValue M H (h + 1) y ≤
        ∑ y : S, empirical hist x a y *
          Finset.univ.sup' Finset.univ_nonempty
            (fun a' : A => qFuel M H K δ hist prevQ (H - (h + 1)) (h + 1) y a') := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hnext' y) (he0 y)
    have h2 := hconf h hh x a hpos
    have h3 : ∑ y : S, (empirical hist x a y - M.P x a y) * optimalValue M H (h + 1) y =
        ∑ y : S, empirical hist x a y * optimalValue M H (h + 1) y -
          ∑ y : S, M.P x a y * optimalValue M H (h + 1) y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _; ring
    unfold Qs
    linarith

lemma inner (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ)
    (hprev : ∀ h, h < H → ∀ x a, Qs M H h x a ≤ prevQ h x a)
    (hconf : ∀ h, h < H → ∀ x a, 0 < countSA hist x a →
      -(bonus (Fintype.card S) (Fintype.card A) H K (countSA hist x a) δ) ≤
        ∑ y : S, (empirical hist x a y - M.P x a y) * optimalValue M H (h + 1) y) :
    ∀ m h, H - h = m → h ≤ H → ∀ y,
      optimalValue M H h y ≤ valueAt (qAt M H K δ hist prevQ) h y := by
  intro m
  induction m with
  | zero =>
    intro h hm hh y
    have hH : h = H := by omega
    subst hH
    have b := (opt_bounds M h h y).2
    simp only [Nat.sub_self, Nat.cast_zero] at b
    refine le_trans b (le_trans ?_ (value_ge _ h y (Classical.arbitrary A)))
    unfold qAt
    simp [Nat.sub_self, qFuel]
  | succ m ih =>
    intro h hm hh y
    have hlt : h < H := by omega
    have hnext := ih (h + 1) (by omega) (by omega)
    apply opt_le_of M H h hlt y
    intro a
    exact le_trans (step M H K δ hist prevQ hprev hconf h hlt hnext y a) (value_ge _ h y a)

lemma inner_Q (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ)
    (hprev : ∀ h, h < H → ∀ x a, Qs M H h x a ≤ prevQ h x a)
    (hconf : ∀ h, h < H → ∀ x a, 0 < countSA hist x a →
      -(bonus (Fintype.card S) (Fintype.card A) H K (countSA hist x a) δ) ≤
        ∑ y : S, (empirical hist x a y - M.P x a y) * optimalValue M H (h + 1) y)
    (h : ℕ) (hh : h < H) (x : S) (a : A) :
    Qs M H h x a ≤ qAt M H K δ hist prevQ h x a :=
  step M H K δ hist prevQ hprev hconf h hh
    (fun y => inner M H K δ hist prevQ hprev hconf (H - (h + 1)) (h + 1) rfl (by omega) y) x a

lemma log_ge_one (H K : ℕ) (hH : 0 < H) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ algorithmLog (Fintype.card S) (Fintype.card A) H K δ := by
  unfold algorithmLog
  have hS : (1:ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hA : (1:ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hKH : (1:ℝ) ≤ ((K * H : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hK hH
  have h5 : (5:ℝ) ≤ 5 * (Fintype.card S : ℝ) * (Fintype.card A) * ((K * H : ℕ) : ℝ) := by
    have h1 : (1:ℝ) ≤ (Fintype.card S : ℝ) * (Fintype.card A) := by nlinarith
    have h2 : (1:ℝ) ≤ (Fintype.card S : ℝ) * (Fintype.card A) * ((K * H : ℕ) : ℝ) := by nlinarith
    nlinarith
  have h6 : (5:ℝ) ≤ 5 * (Fintype.card S : ℝ) * (Fintype.card A) * ((K * H : ℕ) : ℝ) / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma conf_of_event (M : MDP S A) (H K : ℕ) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (init : InitialRule S K H) (ω : Outcomes S K H)
    (hE : confidenceEvent M H K δ sel init ω) (k : Fin K) :
    ∀ h, h < H → ∀ x a, 0 < countSA (priorHistory M H K δ sel init ω k) x a →
      -(bonus (Fintype.card S) (Fintype.card A) H K
          (countSA (priorHistory M H K δ sel init ω k) x a) δ) ≤
        ∑ y : S, (empirical (priorHistory M H K δ sel init ω k) x a y - M.P x a y) *
          optimalValue M H (h + 1) y := by
  intro h hh x a hpos
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hL := log_ge_one (S := S) (A := A) H K hH hK δ hδ hδ1
  have hb0 : 0 ≤ bonus (Fintype.card S) (Fintype.card A) H K
      (countSA (priorHistory M H K δ sel init ω k) x a) δ := by
    unfold bonus
    apply div_nonneg _ (Real.sqrt_nonneg _)
    have : (0:ℝ) ≤ H := Nat.cast_nonneg H
    have : (0:ℝ) ≤ 7 * H := by linarith
    exact mul_nonneg this (by linarith)
  by_cases h1 : h + 1 < H
  · have hev := (hE k ⟨h + 1, h1⟩ x a hpos).1
    have hc := c1_le_bonus (Fintype.card S) (Fintype.card A) H K
      (countSA (priorHistory M H K δ sel init ω k) x a) δ
      (trueVariance M H (h + 1) x a) hpos hL (var_le M H (h + 1) x a)
    have hm := (abs_le.mp (le_trans hev (min_le_left _ _))).1
    have : nAt M H K δ sel init ω k x a = countSA (priorHistory M H K δ sel init ω k) x a := rfl
    rw [this] at hm
    exact le_trans (neg_le_neg hc) hm
  · have hz : ∀ y, optimalValue M H (h + 1) y = 0 := by
      intro y
      have b := opt_bounds M H (h + 1) y
      have : H - (h + 1) = 0 := by omega
      rw [this] at b
      simp only [Nat.cast_zero] at b
      linarith [b.1, b.2]
    simp only [hz, mul_zero, Finset.sum_const_zero]
    linarith

lemma prevQ_bound (M : MDP S A) (H K : ℕ) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (init : InitialRule S K H) (ω : Outcomes S K H)
    (hE : confidenceEvent M H K δ sel init ω) :
    ∀ n h, h < H → ∀ x a, Qs M H h x a ≤ (runPrefix M H K δ sel init ω n).prevQ h x a := by
  intro n
  induction n with
  | zero =>
    intro h hh x a
    simp only [runPrefix]
    exact Qs_le_H M H h hh x a
  | succ n ih =>
    intro h hh x a
    by_cases hn : n < K
    · simp only [runPrefix, dif_pos hn]
      exact inner_Q M H K δ _ _ ih
        (conf_of_event M H K hH δ hδ hδ1 sel init ω hE ⟨n, hn⟩) h hh x a
    · simp only [runPrefix, dif_neg hn]
      exact ih h hh x a

end MinimaxRegretRL.Hoeffding.L18Opt

open MinimaxRegretRL.Hoeffding in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (hH : 0 < H) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) (ω : Outcomes S K H)
    (hE : confidenceEvent M H K δ sel init ω) :
    ∀ (k : Fin K) (h : ℕ) (hh : h ≤ H) (x : S),
      optimalValue M H h x ≤ estimatedValue M H K δ sel init ω k h x := by
  intro k h hh x
  exact L18Opt.inner M H K δ (runPrefix M H K δ sel init ω k.val).history
    (runPrefix M H K δ sel init ω k.val).prevQ
    (L18Opt.prevQ_bound M H K hH δ hδ hδ1 sel init ω hE k.val)
    (L18Opt.conf_of_event M H K hH δ hδ hδ1 sel init ω hE k) (H - h) h rfl hh x
