-- Prove2me | solution 1 for InfoRelaxTS.Gap.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:12:30.84548+00:00
-- url     : https://prove2.me/submissions/b2137d8f-d95d-4746-9416-382f2ca53bd9

import Mathlib
import Definitions.Def_InfoRelaxTS_Gap_Setting

namespace InfoRelaxTS.Gap

private lemma pullsBefore_lt_of_lt {K T : ℕ} (s : Fin T → Fin K) (a : Fin K)
    (t₁ t₂ : Fin T) (h₁ : s t₁ = a) (h12 : t₁ < t₂) :
    pullsBefore s t₁ a < pullsBefore s t₂ a := by
  unfold pullsBefore
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨t₁, ?_, ?_⟩
    · simp [h12, h₁]
    · simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨lt_trans hx.1 h12, hx.2⟩

private lemma pullsBefore_lt_pullCount {K T : ℕ} (s : Fin T → Fin K) (t : Fin T) :
    pullsBefore s t (s t) < pullCount s (s t) := by
  unfold pullsBefore pullCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨t, ?_, ?_⟩
    · simp
    · simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2

/-- Regrouping a sum over time by arms. -/
private lemma sum_regroup {K T : ℕ} (s : Fin T → Fin K) (f : Fin K → ℕ → ℝ) :
    ∑ t, f (s t) (pullsBefore s t (s t)) =
      ∑ a, ∑ n ∈ Finset.range (pullCount s a), f a n := by
  rw [← Finset.sum_fiberwise Finset.univ s]
  refine Finset.sum_congr rfl fun a _ => ?_
  set S := Finset.univ.filter fun t : Fin T => s t = a with hS
  have hfib : ∀ t ∈ S, f (s t) (pullsBefore s t (s t)) = f a (pullsBefore s t a) := by
    intro t ht
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht]
  rw [Finset.sum_congr rfl hfib]
  have hinj : Set.InjOn (fun t => pullsBefore s t a) S := by
    intro x hx y hy hxy
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hxy (ne_of_lt (pullsBefore_lt_of_lt s a x y hx h))
    · exact absurd hxy (ne_of_gt (pullsBefore_lt_of_lt s a y x hy h))
  have hcount : pullCount s a = S.card := rfl
  have himg : S.image (fun t => pullsBefore s t a) = Finset.range (pullCount s a) := by
    apply Finset.eq_of_subset_of_card_le
    · intro n hn
      simp only [Finset.mem_image] at hn
      obtain ⟨t, ht, rfl⟩ := hn
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have := pullsBefore_lt_pullCount s t
      rw [ht] at this
      simpa using this
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range, hcount]
  rw [← himg, Finset.sum_image hinj]


private lemma mem_filter_iff {K T : ℕ} (hT : 1 ≤ T) (s : Fin T → Fin K) (a : Fin K) :
    s ∈ (Finset.univ.filter fun s : Fin T → Fin K => ∀ t : Fin T, t.val = 0 → s t = a) ↔
      s ⟨0, hT⟩ = a := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact h _ rfl
  · intro h t ht
    have : t = ⟨0, hT⟩ := Fin.ext ht
    rw [this]; exact h

private lemma le_Q1 {K T : ℕ} (hT : 1 ≤ T) (pay : (Fin T → Fin K) → Fin T → ℝ) (a : Fin K)
    (s : Fin T → Fin K) (hs : s ⟨0, hT⟩ = a) : ∑ t, pay s t ≤ Q1 pay a := by
  unfold Q1
  exact Finset.le_sup' (fun s => ∑ t, pay s t) ((mem_filter_iff hT s a).mpr hs)

private lemma exists_Q1 {K T : ℕ} (hT : 1 ≤ T) (pay : (Fin T → Fin K) → Fin T → ℝ) (a : Fin K) :
    ∃ s : Fin T → Fin K, s ⟨0, hT⟩ = a ∧ Q1 pay a = ∑ t, pay s t := by
  unfold Q1
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup' (⟨fun _ => a, by simp⟩ :
    (Finset.univ.filter fun s : Fin T → Fin K => ∀ t : Fin T, t.val = 0 → s t = a).Nonempty)
    (fun s => ∑ t, pay s t)
  exact ⟨s, (mem_filter_iff hT s a).mp hs, heq⟩

private lemma sum_update_fin {T : ℕ} {M : Type} [AddCommMonoid M] (f : Fin T → M) (t0 : Fin T)
    (v : M) : ∑ t, Function.update f t0 v t + f t0 = ∑ t, f t + v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ t0),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ t0), Finset.sdiff_singleton_eq_erase]
  abel

private lemma Q1_shift {K T : ℕ} (hT : 1 ≤ T) (g : Fin K → ℝ) (a b : Fin K) :
    Q1 (T := T) (fun s t => g (s t)) b - g b + g a ≤ Q1 (T := T) (fun s t => g (s t)) a := by
  obtain ⟨s, hs0, hQ⟩ := exists_Q1 hT (fun s t => g (s t)) b
  have hmem : Function.update s ⟨0, hT⟩ a ⟨0, hT⟩ = a := by simp
  have h1 := le_Q1 hT (fun s t => g (s t)) a (Function.update s ⟨0, hT⟩ a) hmem
  have hfun : (fun t => g (Function.update s ⟨0, hT⟩ a t)) =
      Function.update (fun t => g (s t)) ⟨0, hT⟩ (g a) := by
    funext t
    by_cases h : t = ⟨0, hT⟩
    · subst h; simp
    · simp [Function.update_apply, h]
  have hsum := sum_update_fin (fun t => g (s t)) ⟨0, hT⟩ (g a)
  rw [← hfun, hs0] at hsum
  try simp only at h1 hQ
  rw [hQ]
  linarith

private lemma Q1_eq {K T : ℕ} (hT : 1 ≤ T) (g : Fin K → ℝ) (aStar a : Fin K) :
    Q1 (T := T) (fun s t => g (s t)) aStar - Q1 (T := T) (fun s t => g (s t)) a =
      g aStar - g a := by
  have h1 := Q1_shift hT g a aStar
  have h2 := Q1_shift hT g aStar a
  linarith

private lemma pullCount_update {K T : ℕ} (s : Fin T → Fin K) (t0 : Fin T) (a b : Fin K) :
    pullCount (Function.update s t0 a) b + (if s t0 = b then 1 else 0) =
      pullCount s b + (if a = b then 1 else 0) := by
  unfold pullCount
  rw [Finset.card_filter, Finset.card_filter]
  have hfun : (fun t => if Function.update s t0 a t = b then 1 else 0) =
      Function.update (fun t => if s t = b then (1 : ℕ) else 0) t0 (if a = b then 1 else 0) := by
    funext t
    by_cases h : t = t0
    · subst h; simp
    · simp [Function.update_apply, h]
  rw [hfun]
  exact sum_update_fin _ _ _

private lemma pullCount_le {K T : ℕ} (s : Fin T → Fin K) (a : Fin K) : pullCount s a ≤ T := by
  unfold pullCount
  calc (Finset.univ.filter fun t : Fin T => s t = a).card ≤ (Finset.univ : Finset (Fin T)).card :=
        Finset.card_filter_le _ _
    _ = T := by simp

theorem solution_aux {K : ℕ} (T : ℕ) (hT : 1 ≤ T) (μv : Fin K → ℝ) (m : Fin K → ℕ → ℝ) :
    (∀ aStar : Fin K, (∀ a', Q1 (payTS (T := T) μv) a' ≤ Q1 (payTS (T := T) μv) aStar) →
      ∀ a, Q1 (payTS (T := T) μv) aStar - Q1 (payTS (T := T) μv) a = μv aStar - μv a) ∧
    (∀ aStar : Fin K, (∀ a', Q1 (payFH (T := T) m) a' ≤ Q1 (payFH (T := T) m) aStar) →
      ∀ a, Q1 (payFH (T := T) m) aStar - Q1 (payFH (T := T) m) a = m aStar (T - 1) - m a (T - 1)) ∧
    (∀ aStar : Fin K, (∀ a', Q1 (payVZ (T := T) m) a' ≤ Q1 (payVZ (T := T) m) aStar) →
      ∀ a, Q1 (payVZ (T := T) m) a < Q1 (payVZ (T := T) m) aStar →
        Q1 (payVZ (T := T) m) aStar - Q1 (payVZ (T := T) m) a ≤
          (Finset.range T).sup' (Finset.nonempty_range_iff.mpr (by omega)) (fun n => m aStar n)
            - m a 0) := by
  refine ⟨fun aStar _ a => Q1_eq hT μv aStar a,
    fun aStar _ a => Q1_eq hT (fun b => m b (T - 1)) aStar a, ?_⟩
  intro aStar _ a hlt
  obtain ⟨s, hs0, hQ⟩ := exists_Q1 hT (payVZ (T := T) m) aStar
  have hpay : ∀ s' : Fin T → Fin K, ∑ t, payVZ (T := T) m s' t =
      ∑ b, ∑ n ∈ Finset.range (pullCount s' b), m b n := fun s' => sum_regroup s' m
  by_cases hpos : 0 < pullCount s a
  · exfalso
    obtain ⟨t, ht⟩ : ∃ t, s t = a := by
      unfold pullCount at hpos
      obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ⟨t, ht⟩
    have hcnt : ∀ b, pullCount (s ∘ Equiv.swap ⟨0, hT⟩ t) b = pullCount s b := by
      intro b
      unfold pullCount
      apply Finset.card_equiv (Equiv.swap ⟨0, hT⟩ t)
      intro i
      simp
    have h1 := le_Q1 hT (payVZ (T := T) m) a (s ∘ Equiv.swap ⟨0, hT⟩ t)
      (by simp [Equiv.swap_apply_left, ht])
    rw [hpay] at h1
    simp_rw [hcnt] at h1
    rw [← hpay, ← hQ] at h1
    linarith
  · have hzero : pullCount s a = 0 := by omega
    have haa : a ≠ aStar := by
      intro h; rw [h] at hlt; exact lt_irrefl _ hlt
    set s' := Function.update s ⟨0, hT⟩ a with hs'
    have hc : ∀ b, pullCount s' b + (if aStar = b then 1 else 0) =
        pullCount s b + (if a = b then 1 else 0) := by
      intro b
      have := pullCount_update s ⟨0, hT⟩ a b
      rw [hs0] at this
      exact this
    have h1 := le_Q1 hT (payVZ (T := T) m) a s' (by simp [hs'])
    have hb : ∀ b, ∑ n ∈ Finset.range (pullCount s b), m b n -
        ∑ n ∈ Finset.range (pullCount s' b), m b n =
        (if b = aStar then m aStar (pullCount s' aStar) else 0) -
          (if b = a then m a 0 else 0) := by
      intro b
      have hcb := hc b
      by_cases hbs : b = aStar
      · have hba : b ≠ a := fun h => haa (h.symm.trans hbs)
        rw [if_pos hbs, if_neg hba]
        rw [if_pos hbs.symm, if_neg (fun h => hba h.symm)] at hcb
        rw [hbs] at hcb ⊢
        have hN : pullCount s aStar = pullCount s' aStar + 1 := by omega
        rw [hN, Finset.sum_range_succ]
        ring
      · by_cases hba : b = a
        · rw [if_neg hbs, if_pos hba]
          rw [if_neg (fun h => hbs h.symm), if_pos hba.symm] at hcb
          rw [hba] at hcb ⊢
          have hN' : pullCount s' a = 1 := by omega
          rw [hzero, hN']
          simp
        · rw [if_neg hbs, if_neg hba]
          rw [if_neg (fun h => hbs h.symm), if_neg (fun h => hba h.symm)] at hcb
          have hN : pullCount s b = pullCount s' b := by omega
          rw [hN]
          ring
    have htot : ∑ b, ∑ n ∈ Finset.range (pullCount s b), m b n -
        ∑ b, ∑ n ∈ Finset.range (pullCount s' b), m b n =
        m aStar (pullCount s' aStar) - m a 0 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun b _ => hb b),
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp
    have hlt' : pullCount s' aStar < T := by
      have h1 := hc aStar
      have h2 := pullCount_le s aStar
      rw [if_pos rfl, if_neg haa] at h1
      omega
    have hle : m aStar (pullCount s' aStar) ≤
        (Finset.range T).sup' (Finset.nonempty_range_iff.mpr (by omega)) (fun n => m aStar n) :=
      Finset.le_sup' (fun n => m aStar n) (Finset.mem_range.mpr hlt')
    rw [hQ, hpay]
    rw [hpay] at h1
    linarith

end InfoRelaxTS.Gap

open InfoRelaxTS.Gap in
theorem solution {K : ℕ} (T : ℕ) (hT : 1 ≤ T) (μv : Fin K → ℝ) (m : Fin K → ℕ → ℝ) :
    (∀ aStar : Fin K, (∀ a', Q1 (payTS (T := T) μv) a' ≤ Q1 (payTS (T := T) μv) aStar) →
      ∀ a, Q1 (payTS (T := T) μv) aStar - Q1 (payTS (T := T) μv) a = μv aStar - μv a) ∧
    (∀ aStar : Fin K, (∀ a', Q1 (payFH (T := T) m) a' ≤ Q1 (payFH (T := T) m) aStar) →
      ∀ a, Q1 (payFH (T := T) m) aStar - Q1 (payFH (T := T) m) a = m aStar (T - 1) - m a (T - 1)) ∧
    (∀ aStar : Fin K, (∀ a', Q1 (payVZ (T := T) m) a' ≤ Q1 (payVZ (T := T) m) aStar) →
      ∀ a, Q1 (payVZ (T := T) m) a < Q1 (payVZ (T := T) m) aStar →
        Q1 (payVZ (T := T) m) aStar - Q1 (payVZ (T := T) m) a ≤
          (Finset.range T).sup' (Finset.nonempty_range_iff.mpr (by omega)) (fun n => m aStar n)
            - m a 0) :=
  InfoRelaxTS.Gap.solution_aux T hT μv m
