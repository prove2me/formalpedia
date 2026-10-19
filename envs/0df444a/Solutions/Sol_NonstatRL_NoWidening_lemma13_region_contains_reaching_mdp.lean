-- Prove2me | solution 1 for NonstatRL.NoWidening.lemma13_region_contains_reaching_mdp
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T09:18:19.99645+00:00
-- url     : https://prove2.me/submissions/ecd5f47e-0648-46a0-a6c9-cd4b991c4b9d

import Definitions.Def_NonstatRL_PerStep_Window
set_option autoImplicit false
open BanditAlgorithm NonstatRL.PerStep
open scoped NNReal
noncomputable section
namespace NonstatRL.NoWidening

lemma countPlus_pos {S A : ℕ} (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (s : Fin S) (a : Fin A) : 0 < countPlus st ac lo hi s a := by
  unfold countPlus
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))

lemma average_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (lo hi : ℕ) (s : Fin S) (a : Fin A) (y : Fin S) :
    0 ≤ pBar M st ac lo hi s a y := by
  unfold pBar
  apply div_nonneg _ (countPlus_pos st ac lo hi s a).le
  exact Finset.sum_nonneg (fun q _ => by split_ifs <;> positivity)

lemma average_sum {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (lo hi : ℕ) (s : Fin S) (a : Fin A)
    (hc : 0 < count st ac lo hi s a) : ∑ y, pBar M st ac lo hi s a y = 1 := by
  unfold pBar
  rw [← Finset.sum_div,Finset.sum_comm]
  have hsum : (∑ q ∈ Finset.Ico lo hi, ∑ y : Fin S,
      if st q=s ∧ ac q=a then ((M q).P s a y : ℝ) else 0) = count st ac lo hi s a := by
    calc
      _ = ∑ q ∈ Finset.Ico lo hi, if st q=s ∧ ac q=a then (1:ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases h : st q=s ∧ ac q=a
        · simp only [if_pos h]
          exact_mod_cast (M q).P_sum_one s a
        · simp [h]
      _ = _ := by simp [count,Finset.sum_boole]
  rw [hsum]
  unfold countPlus
  rw [max_eq_right hc]
  exact div_self (by exact_mod_cast Nat.ne_of_gt hc)

lemma average_lower {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (lo hi : ℕ) (s : Fin S) (a : Fin A) (y : Fin S)
    (hc : 0 < count st ac lo hi s a) (z : ℝ)
    (hz : ∀ q ∈ Finset.Ico lo hi, z ≤ ((M q).P s a y : ℝ)) :
    z ≤ pBar M st ac lo hi s a y := by
  unfold pBar
  apply (le_div_iff₀ (countPlus_pos st ac lo hi s a)).mpr
  have hsum := Finset.sum_le_sum (s := Finset.Ico lo hi) (f := fun q => if st q=s ∧ ac q=a then z else 0)
    (g := fun q => if st q=s ∧ ac q=a then ((M q).P s a y : ℝ) else 0)
    (fun q hq => by split_ifs <;> first | exact hz q hq | exact le_rfl)
  have hid : (∑ q ∈ Finset.Ico lo hi, if st q=s ∧ ac q=a then z else 0) =
      (count st ac lo hi s a : ℝ)*z := by
    rw [← Finset.sum_filter]
    simp [count]
  rw [hid] at hsum
  unfold countPlus
  rw [max_eq_right hc]
  simpa [mul_comm] using hsum

lemma phat_zero {S A : ℕ} (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (s : Fin S) (a : Fin A)
    (hz : count st ac lo hi s a=0) : ∀ y, pHat st ac lo hi s a y=0 := by
  have hempty : ((Finset.Ico lo hi).filter (fun q => st q=s ∧ ac q=a))=∅ := Finset.card_eq_zero.mp hz
  intro y
  have hsubset : ((Finset.Ico lo hi).filter (fun q => st q=s ∧ ac q=a ∧ st (q+1)=y)) ⊆
      ((Finset.Ico lo hi).filter (fun q => st q=s ∧ ac q=a)) := by
    intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1,hq.2.1,hq.2.2.1⟩
  rw [hempty] at hsubset
  have hnil := Finset.subset_empty.mp hsubset
  simp [pHat,hnil]

lemma radius_one {S A : ℕ} (hS : 1 < S)
    (As : Fin S → Finset (Fin A)) (hAs : ∀ s, (As s).Nonempty)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    1 ≤ radP As T δ 1 := by
  have hs : (2:ℝ) ≤ S := by exact_mod_cast hS
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have htotal : (S:ℝ) ≤ ∑ s : Fin S, ((As s).card : ℝ) := by
    calc
      _ = ∑ s : Fin S, (1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun s _ => by exact_mod_cast (Finset.card_pos.mpr (hAs s)))
  have hnum : 2 ≤ (∑ s : Fin S, ((As s).card : ℝ))*(T:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ ∑ s : Fin S, ((As s).card : ℝ) from by positivity)]
  have harg : 2 ≤ (∑ s : Fin S, ((As s).card : ℝ))*(T:ℝ)/δ := by
    apply (le_div_iff₀ hδ.1).mpr
    linarith [hδ.2]
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hlog : (1/2:ℝ) ≤ Real.log ((∑ s : Fin S, ((As s).card : ℝ))*T/δ) :=
    hlog2.trans (Real.log_le_log (by norm_num) harg)
  have hinside : 1 ≤ 2*(S:ℝ)*Real.log ((∑ s : Fin S, ((As s).card : ℝ))*T/δ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (show 0≤2*(S:ℝ) from by positivity)]
  have hroot := Real.sqrt_le_sqrt hinside
  simp only [Real.sqrt_one] at hroot
  unfold radP
  rw [div_one]
  linarith

lemma unvisited_core {S A : ℕ} (hS : 1 < S)
    (As : Fin S → Finset (Fin A)) (hAs : ∀ s, (As s).Nonempty)
    (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (lo hi : ℕ)
    (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (hzero : count st ac lo hi s a = 0) :
    1 ≤ radP As T δ (countPlus st ac lo hi s a) ∧
      ∀ p : Fin S → ℝ, (∀ s', 0 ≤ p s') → (∑ s', p s') = 1 →
        p ∈ Hp As T δ st ac lo hi 0 s a := by
  have hplus : countPlus st ac lo hi s a=1 := by simp [countPlus,hzero]
  have hr : 1 ≤ radP As T δ (countPlus st ac lo hi s a) := by rw [hplus]; exact radius_one hS As hAs T hT δ hδ
  refine ⟨hr,?_⟩
  intro p hp hs
  refine ⟨hp,hs,?_⟩
  simp only [phat_zero st ac lo hi s a hzero,sub_zero,abs_of_nonneg (hp _),add_zero]
  rwa [hs]


lemma visited_core {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t : ℕ)
    (hτ : τm ≤ t) (ht : t < T)
    (ζ : ℝ) (hζ : 0 < ζ) (a₂ : Fin S → Fin S → Fin A)
    (ha₂ : ∀ s s', a₂ s s' ∈ As s)
    (hreach : ∀ q < T, ∀ s s', ζ ≤ ((M q).P s (a₂ s s') s' : ℝ))
    (hEp : NonstatRL.PerStep.EventP M As T δ st ac (τm - W) t) :
    ∀ s s', 0 < NonstatRL.PerStep.count st ac (τm - W) t s (a₂ s s') →
      ζ ≤ NonstatRL.PerStep.pBar M st ac (τm - W) t s (a₂ s s') s' ∧
      (fun y => NonstatRL.PerStep.pBar M st ac (τm - W) t s (a₂ s s') y) ∈
        NonstatRL.PerStep.Hp As T δ st ac (τm - W) t 0 s (a₂ s s') := by
  intro s s' hc
  refine ⟨average_lower M st ac (τm-W) t s (a₂ s s') s' hc ζ ?_,?_⟩
  · intro q hq
    exact hreach q ((Finset.mem_Ico.mp hq).2.trans ht) s s'
  · refine ⟨average_nonneg M st ac (τm-W) t s (a₂ s s'),
      average_sum M st ac (τm-W) t s (a₂ s s') hc,?_⟩
    simpa only [add_zero] using hEp s (a₂ s s') (ha₂ s s')



lemma model_core {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t : ℕ)
    (hτ : τm ≤ t) (ht : t < T)
    (ζ : ℝ) (hζ : 0 < ζ) (a₂ : Fin S → Fin S → Fin A)
    (ha₂ : ∀ s s', a₂ s s' ∈ As s)
    (hreach : ∀ q < T, ∀ s s', ζ ≤ ((M q).P s (a₂ s s') s' : ℝ))
    (hEp : NonstatRL.PerStep.EventP M As T δ st ac (τm - W) t) :
    ∃ Mw : FiniteMDP S A,
      (∀ s, ∀ a ∈ As s,
        (fun s' => (Mw.P s a s' : ℝ)) ∈ NonstatRL.PerStep.Hp As T δ st ac (τm - W) t 0 s a) ∧
      ∀ s s', ζ ≤ (Mw.P s (a₂ s s') s' : ℝ) := by
  classical
  let Q : Fin S → Fin A → Fin S → ℝ := fun s a y =>
    if count st ac (τm-W) t s a=0 then ((M 0).P s a y : ℝ)
    else pBar M st ac (τm-W) t s a y
  have hQ0 (s : Fin S) (a : Fin A) (y : Fin S) : 0 ≤ Q s a y := by
    dsimp [Q]
    split_ifs
    · positivity
    · exact average_nonneg M st ac (τm-W) t s a y
  have hQsum (s : Fin S) (a : Fin A) : ∑ y, Q s a y=1 := by
    by_cases hc : count st ac (τm-W) t s a=0
    · simp only [Q,if_pos hc]
      exact_mod_cast (M 0).P_sum_one s a
    · simpa only [Q,if_neg hc] using average_sum M st ac (τm-W) t s a (Nat.pos_of_ne_zero hc)
  let Mw : FiniteMDP S A := {
    P := fun s a y => Real.toNNReal (Q s a y)
    P_sum_one := fun s a => by
      apply NNReal.coe_injective
      simpa only [NNReal.coe_sum,Real.coe_toNNReal _ (hQ0 _ _ _),NNReal.coe_one] using hQsum s a
    r := fun _ _ => 0
    r_mem_Icc := fun _ _ => by simp }
  refine ⟨Mw,?_,?_⟩
  · intro s a ha
    change (fun y => (Real.toNNReal (Q s a y) : ℝ)) ∈ Hp As T δ st ac (τm-W) t 0 s a
    simp only [Real.coe_toNNReal _ (hQ0 _ _ _)]
    by_cases hc : count st ac (τm-W) t s a=0
    · have hT : 1 ≤ T := Nat.zero_lt_of_lt ht
      apply (unvisited_core hS As hAs T hT δ hδ st ac (τm-W) t s a ha hc).2
      · exact hQ0 s a
      · exact hQsum s a
    · refine ⟨hQ0 s a,hQsum s a,?_⟩
      simpa only [Q,if_neg hc,add_zero] using hEp s a ha
  · intro s s'
    change ζ ≤ (Real.toNNReal (Q s (a₂ s s') s') : ℝ)
    rw [Real.coe_toNNReal _ (hQ0 _ _ _)]
    by_cases hc : count st ac (τm-W) t s (a₂ s s')=0
    · simpa only [Q,if_pos hc] using hreach 0 (Nat.zero_lt_of_lt ht) s s'
    · simpa only [Q,if_neg hc] using
        (visited_core hS M As hAs T δ hδ st ac W τm t hτ ht ζ hζ a₂ ha₂ hreach hEp s s' (Nat.pos_of_ne_zero hc)).1


end NonstatRL.NoWidening

open NonstatRL.NoWidening

theorem solution {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t : ℕ)
    (hτ : τm ≤ t) (ht : t < T)
    (ζ : ℝ) (hζ : 0 < ζ) (a₂ : Fin S → Fin S → Fin A)
    (ha₂ : ∀ s s', a₂ s s' ∈ As s)
    (hreach : ∀ q < T, ∀ s s', ζ ≤ ((M q).P s (a₂ s s') s' : ℝ))
    (hEp : NonstatRL.PerStep.EventP M As T δ st ac (τm - W) t) :
    ∃ Mw : FiniteMDP S A,
      (∀ s, ∀ a ∈ As s,
        (fun s' => (Mw.P s a s' : ℝ)) ∈ NonstatRL.PerStep.Hp As T δ st ac (τm - W) t 0 s a) ∧
      ∀ s s', ζ ≤ (Mw.P s (a₂ s s') s' : ℝ) := by exact model_core hS M As hAs T δ hδ st ac W τm t hτ ht ζ hζ a₂ ha₂ hreach hEp


#print axioms solution
