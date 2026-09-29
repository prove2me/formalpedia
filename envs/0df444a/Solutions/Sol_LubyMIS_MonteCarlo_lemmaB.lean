-- Prove2me | solution 1 for LubyMIS.MonteCarlo.lemmaB
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:47:34.820746+00:00
-- url     : https://prove2.me/submissions/87aab9c0-e530-454b-9291-273d71d49a9f

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic



namespace LubyMIS.MonteCarlo

open Classical Finset

section LB
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

lemma lb_coin_nonneg (i : V) : 0 ≤ coinProb H i := by
  unfold coinProb; split_ifs <;> positivity

lemma lb_coin_le (i : V) : coinProb H i ≤ 1 := by
  unfold coinProb; split_ifs with h
  · have : (1:ℝ) ≤ H.degree i := by exact_mod_cast h
    rw [div_le_one (by positivity)]; linarith
  · exact le_rfl

lemma lb_w_nonneg (i : V) (b : Bool) :
    0 ≤ (if b then coinProb H i else 1 - coinProb H i) := by
  have := lb_coin_nonneg H i; have := lb_coin_le H i
  split_ifs <;> linarith

lemma lb_law_nonneg (c : V → Bool) : 0 ≤ lawB H c := by
  unfold lawB; exact Finset.prod_nonneg (fun i _ => lb_w_nonneg H i (c i))

lemma lb_law_sum : ∑ c : V → Bool, lawB H c = 1 := by
  unfold lawB
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b then coinProb H i else 1 - coinProb H i)]
  simp

lemma lb_prob_mono {P Q : (V → Bool) → Prop} (h : ∀ c, P c → Q c) :
    probB H P ≤ probB H Q := by
  unfold probB
  apply Finset.sum_le_sum; intro c _
  have := lb_law_nonneg H c
  by_cases hp : P c
  · rw [if_pos hp, if_pos (h c hp)]
  · rw [if_neg hp]; split_ifs <;> linarith

lemma lb_prob_congr {P Q : (V → Bool) → Prop} (h : ∀ c, P c ↔ Q c) :
    probB H P = probB H Q :=
  le_antisymm (lb_prob_mono H fun c => (h c).1) (lb_prob_mono H fun c => (h c).2)

lemma lb_prob_split (P Q : (V → Bool) → Prop) :
    probB H P = probB H (fun c => P c ∧ Q c) + probB H (fun c => P c ∧ ¬ Q c) := by
  unfold probB; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro c _
  by_cases hp : P c <;> by_cases hq : Q c <;> simp [hp, hq]

lemma lb_prob_nonneg (P : (V → Bool) → Prop) : 0 ≤ probB H P := by
  unfold probB; apply Finset.sum_nonneg; intro c _
  have := lb_law_nonneg H c; split_ifs <;> linarith

lemma lb_prob_false : probB H (fun _ => False) = 0 := by simp [probB]
lemma lb_prob_true : probB H (fun _ => True) = 1 := by simp [probB, lb_law_sum]

lemma lb_union (T : Finset V) (Q : V → (V → Bool) → Prop) :
    probB H (fun c => ∃ k ∈ T, Q k c) ≤ ∑ k ∈ T, probB H (Q k) := by
  unfold probB
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro c _
  have hl := lb_law_nonneg H c
  split_ifs with h
  · obtain ⟨k, hk, hq⟩ := h
    calc lawB H c = (if Q k c then lawB H c else 0) := by rw [if_pos hq]
      _ ≤ ∑ k ∈ T, (if Q k c then lawB H c else 0) :=
        Finset.single_le_sum (f := fun k => if Q k c then lawB H c else 0)
          (fun k _ => by split_ifs <;> linarith) hk
  · apply Finset.sum_nonneg; intro k _; split_ifs <;> linarith

lemma lb_ite_iff {p q : Prop} {_ : Decidable p} {_ : Decidable q} (h : p ↔ q) (a b : ℝ) :
    (if p then a else b) = (if q then a else b) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg (mt h.2 hp)]

def flipAt (k : V) (c : V → Bool) : V → Bool := Function.update c k (!c k)

lemma flipAt_invol (k : V) : Function.Involutive (flipAt k : (V → Bool) → V → Bool) := by
  intro c; funext v; by_cases hv : v = k
  · subst hv; simp [flipAt]
  · simp [flipAt, Function.update_of_ne hv]

lemma lb_law_split (k : V) (c : V → Bool) : lawB H c =
    (if c k then coinProb H k else 1 - coinProb H k) *
      ∏ x ∈ univ.erase k, (if c x then coinProb H x else 1 - coinProb H x) := by
  unfold lawB
  exact (Finset.mul_prod_erase univ (fun x => if c x then coinProb H x else 1 - coinProb H x)
    (mem_univ k)).symm

lemma lb_law_flip (k : V) (c : V → Bool) (hck : c k = true) :
    lawB H c = coinProb H k * (lawB H c + lawB H (flipAt k c)) := by
  have hR : ∏ x ∈ univ.erase k, (if flipAt k c x then coinProb H x else 1 - coinProb H x)
      = ∏ x ∈ univ.erase k, (if c x then coinProb H x else 1 - coinProb H x) := by
    apply Finset.prod_congr rfl; intro x hx
    rw [Finset.mem_erase] at hx
    simp [flipAt, Function.update_of_ne hx.1]
  have e : flipAt k c k = false := by simp [flipAt, hck]
  rw [lb_law_split H k c, lb_law_split H k (flipAt k c), hR, e, hck]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

lemma lb_indep (k : V) (P : (V → Bool) → Prop) (hP : ∀ c, P (flipAt k c) ↔ P c) :
    probB H (fun c => P c ∧ c k = true) = coinProb H k * probB H P := by
  have hs := lb_prob_split H P (fun c => c k = true)
  have h2 : probB H (fun c => P c ∧ ¬ c k = true)
      = ∑ c, (if P c ∧ c k = true then lawB H (flipAt k c) else 0) := by
    unfold probB
    rw [← Equiv.sum_comp (flipAt_invol k).toPerm]
    apply Finset.sum_congr rfl; intro c _
    simp only [Function.Involutive.coe_toPerm]
    have hiff : (P (flipAt k c) ∧ ¬ flipAt k c k = true) ↔ (P c ∧ c k = true) := by
      rw [hP]; simp [flipAt]
    exact lb_ite_iff hiff _ _
  rw [hs, h2]
  unfold probB
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  by_cases h : P c ∧ c k = true
  · rw [if_pos h, if_pos h]; exact lb_law_flip H k c h.2
  · rw [if_neg h, if_neg h]; simp

lemma lb_indep_false (k : V) (P : (V → Bool) → Prop) (hP : ∀ c, P (flipAt k c) ↔ P c) :
    probB H (fun c => P c ∧ c k = false) = (1 - coinProb H k) * probB H P := by
  have hs := lb_prob_split H P (fun c => c k = true)
  have h1 := lb_indep H k P hP
  have h3 : probB H (fun c => P c ∧ ¬ c k = true) = probB H (fun c => P c ∧ c k = false) :=
    lb_prob_congr H (fun c => by simp)
  linarith

lemma mem_selectB_iff (c : V → Bool) (a : V) : a ∈ selectB H c ↔
    c a = true ∧ ∀ j, H.Adj a j → c j = true → H.degree j < H.degree a := by
  simp [selectB]

lemma lb_step (S : Finset V) (a : V) (ha : a ∉ S) :
    probB H (fun c => (∀ j ∈ S, c j = false) ∧ a ∈ selectB H c) ≥
      1/2 * probB H (fun c => (∀ j ∈ S, c j = false) ∧ c a = true) := by
  set X := probB H (fun c => (∀ j ∈ S, c j = false) ∧ c a = true) with hX
  let K := (H.neighborFinset a).filter (fun k => H.degree a ≤ H.degree k)
  have hsplit := lb_prob_split H (fun c => (∀ j ∈ S, c j = false) ∧ c a = true)
    (fun c => a ∈ selectB H c)
  have h1 : probB H (fun c => ((∀ j ∈ S, c j = false) ∧ c a = true) ∧ a ∈ selectB H c)
      = probB H (fun c => (∀ j ∈ S, c j = false) ∧ a ∈ selectB H c) :=
    lb_prob_congr H (fun c => by rw [mem_selectB_iff]; tauto)
  have h2 : probB H (fun c => ((∀ j ∈ S, c j = false) ∧ c a = true) ∧ ¬ a ∈ selectB H c)
      ≤ probB H (fun c => ∃ k ∈ K, ((∀ j ∈ S, c j = false) ∧ c a = true) ∧ c k = true) := by
    apply lb_prob_mono; intro c ⟨hc, hn⟩
    rw [mem_selectB_iff] at hn
    push_neg at hn
    obtain ⟨j, hj1, hj2, hj3⟩ := hn hc.2
    exact ⟨j, by simp [K, hj1, hj3], hc, hj2⟩
  have h3 := lb_union H K (fun k c => ((∀ j ∈ S, c j = false) ∧ c a = true) ∧ c k = true)
  have hX0 : 0 ≤ X := lb_prob_nonneg H _
  have h4 : ∀ k ∈ K, probB H (fun c => ((∀ j ∈ S, c j = false) ∧ c a = true) ∧ c k = true)
      ≤ 1 / (2 * (H.degree a : ℝ)) * X := by
    intro k hk
    simp only [K, mem_filter, SimpleGraph.mem_neighborFinset] at hk
    have hda : 1 ≤ H.degree a := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨k, by simpa using hk.1⟩
    have hdk : 1 ≤ H.degree k := le_trans hda hk.2
    by_cases hkS : k ∈ S
    · calc _ ≤ probB H (fun _ => False) := lb_prob_mono H (fun c hc => by
              have := hc.1.1 k hkS; rw [hc.2] at this; exact Bool.noConfusion this)
        _ = 0 := lb_prob_false H
        _ ≤ _ := by positivity
    · have hka : k ≠ a := fun h => by subst h; exact H.irrefl hk.1
      rw [lb_indep H k _ (fun c => by
        have hne : ∀ j ∈ S, flipAt k c j = c j := fun j hj => by
          simp [flipAt, Function.update_of_ne (show j ≠ k from fun h => hkS (h ▸ hj))]
        have hna : flipAt k c a = c a := by simp [flipAt, Function.update_of_ne (Ne.symm hka)]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨fun j hj => (hne j hj) ▸ h1 j hj, hna ▸ h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨fun j hj => (hne j hj).symm ▸ h1 j hj, hna.symm ▸ h2⟩)]
      apply mul_le_mul_of_nonneg_right _ hX0
      unfold coinProb; rw [if_pos hdk]
      have : (H.degree a : ℝ) ≤ H.degree k := by exact_mod_cast hk.2
      have : (1:ℝ) ≤ H.degree a := by exact_mod_cast hda
      apply one_div_le_one_div_of_le (by positivity); linarith
  have h5 : ∑ k ∈ K, probB H (fun c => ((∀ j ∈ S, c j = false) ∧ c a = true) ∧ c k = true)
      ≤ 1/2 * X := by
    calc _ ≤ ∑ k ∈ K, 1 / (2 * (H.degree a : ℝ)) * X := Finset.sum_le_sum h4
      _ = (K.card : ℝ) * (1 / (2 * (H.degree a : ℝ)) * X) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1/2 * X := by
        have hK : K.card ≤ H.degree a := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]; exact Finset.card_filter_le _ _
        rcases Nat.eq_zero_or_pos (H.degree a) with h0 | h0
        · have : K.card = 0 := by omega
          rw [this]; simp; positivity
        · have hK' : (K.card : ℝ) ≤ H.degree a := by exact_mod_cast hK
          have hd : (0:ℝ) < H.degree a := by exact_mod_cast h0
          calc (K.card : ℝ) * (1 / (2 * (H.degree a : ℝ)) * X)
              ≤ (H.degree a : ℝ) * (1 / (2 * (H.degree a : ℝ)) * X) :=
                mul_le_mul_of_nonneg_right hK' (by positivity)
            _ = 1/2 * X := by field_simp
  rw [ge_iff_le, ← h1]
  linarith

lemma lb_main (S : Finset V) :
    probB H (fun c => ∃ j ∈ S, j ∈ selectB H c) ≥
        1/2 * (1 - probB H (fun c => ∀ j ∈ S, c j = false)) ∧
      probB H (fun c => ∀ j ∈ S, c j = false) = ∏ j ∈ S, (1 - coinProb H j) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [lb_prob_congr H (Q := fun _ => False) (fun c => by simp),
      lb_prob_congr H (P := fun c => ∀ j ∈ (∅ : Finset V), c j = false) (Q := fun _ => True)
        (fun c => by simp), lb_prob_false, lb_prob_true]
    simp
  | insert a S ha ih =>
    obtain ⟨ihA, ihF⟩ := ih
    have hP : ∀ c, (∀ j ∈ S, flipAt a c j = false) ↔ (∀ j ∈ S, c j = false) := by
      intro c
      have hne : ∀ j ∈ S, flipAt a c j = c j := fun j hj => by
        simp [flipAt, Function.update_of_ne (show j ≠ a from fun h => ha (h ▸ hj))]
      exact ⟨fun h j hj => (hne j hj) ▸ h j hj, fun h j hj => (hne j hj).symm ▸ h j hj⟩
    have hF' : probB H (fun c => ∀ j ∈ insert a S, c j = false)
        = (1 - coinProb H a) * probB H (fun c => ∀ j ∈ S, c j = false) := by
      rw [← lb_indep_false H a (fun c => ∀ j ∈ S, c j = false) hP]
      exact lb_prob_congr H (fun c => by simp [Finset.mem_insert]; tauto)
    have hT := lb_indep H a (fun c => ∀ j ∈ S, c j = false) hP
    have hstep := lb_step H S a ha
    have hs := lb_prob_split H (fun c => ∃ j ∈ insert a S, j ∈ selectB H c)
      (fun c => ∃ j ∈ S, j ∈ selectB H c)
    have e1 : probB H (fun c => (∃ j ∈ insert a S, j ∈ selectB H c) ∧ ∃ j ∈ S, j ∈ selectB H c)
        = probB H (fun c => ∃ j ∈ S, j ∈ selectB H c) :=
      lb_prob_congr H (fun c => ⟨fun h => h.2, fun h => ⟨by
        obtain ⟨j, hj, hj'⟩ := h; exact ⟨j, Finset.mem_insert_of_mem hj, hj'⟩, h⟩⟩)
    have e2 : probB H (fun c => (∀ j ∈ S, c j = false) ∧ a ∈ selectB H c) ≤
        probB H (fun c => (∃ j ∈ insert a S, j ∈ selectB H c) ∧ ¬ ∃ j ∈ S, j ∈ selectB H c) := by
      apply lb_prob_mono; rintro c ⟨hF, hsel⟩
      refine ⟨⟨a, Finset.mem_insert_self a S, hsel⟩, ?_⟩
      rintro ⟨j, hj, hj'⟩
      rw [mem_selectB_iff] at hj'
      have := hF j hj; rw [hj'.1] at this; exact Bool.noConfusion this
    refine ⟨?_, by rw [hF', ihF, Finset.prod_insert ha]⟩
    rw [hF']
    have hc0 := lb_coin_nonneg H a
    rw [ge_iff_le] at ihA hstep ⊢
    nlinarith

theorem lemmaB_core (i : V) :
    probB H (fun c => i ∈ nbhd H (selectB H c)) ≥ 1 / 4 * min (sumInv H i / 2) 1 := by
  obtain ⟨hA, hF⟩ := lb_main H (H.neighborFinset i)
  have hcongr : probB H (fun c => i ∈ nbhd H (selectB H c))
      = probB H (fun c => ∃ j ∈ H.neighborFinset i, j ∈ selectB H c) :=
    lb_prob_congr H (fun c => by
      simp only [nbhd, mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨j, h1, h2⟩; exact ⟨j, h2, h1⟩
      · rintro ⟨j, h1, h2⟩; exact ⟨j, h2, h1⟩)
  set s := sumInv H i / 2 with hs
  have hsum : s = ∑ j ∈ H.neighborFinset i, coinProb H j := by
    rw [hs, sumInv, Finset.sum_div]
    apply Finset.sum_congr rfl; intro j hj
    rw [SimpleGraph.mem_neighborFinset] at hj
    have hdj : 1 ≤ H.degree j := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨i, by simpa using hj.symm⟩
    unfold coinProb; rw [if_pos hdj]; field_simp
  have hs0 : 0 ≤ s := by rw [hsum]; exact Finset.sum_nonneg (fun j _ => lb_coin_nonneg H j)
  have hprod : ∏ j ∈ H.neighborFinset i, (1 - coinProb H j) ≤ Real.exp (-s) := by
    rw [hsum, ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro j _; linarith [lb_coin_le H j]
    · intro j _; linarith [Real.add_one_le_exp (-coinProb H j)]
  have hexp : Real.exp (-s) ≤ 1 / (1 + s) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by linarith)
    linarith [Real.add_one_le_exp s]
  have hkey : 1 - 1 / (1 + s) ≥ 1/2 * min s 1 := by
    rcases le_or_gt s 1 with h | h
    · rw [min_eq_left h]
      rw [ge_iff_le, ← sub_nonneg]
      have : 1 - 1 / (1 + s) - 1/2 * s = s * (1 - s) / (2 * (1 + s)) := by
        field_simp; ring
      rw [this]; apply div_nonneg (mul_nonneg hs0 (by linarith)) (by linarith)
    · rw [min_eq_right h.le]
      rw [ge_iff_le, ← sub_nonneg]
      have : 1 - 1 / (1 + s) - 1/2 * 1 = (s - 1) / (2 * (1 + s)) := by
        field_simp; ring
      rw [this]; apply div_nonneg (by linarith) (by linarith)
  rw [hcongr]
  rw [hF] at hA
  linarith [hprod, hexp, hkey]

end LB

end LubyMIS.MonteCarlo

open LubyMIS.MonteCarlo


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) (hi : 1 ≤ H.degree i) :
    probB H (fun c => i ∈ nbhd H (selectB H c)) ≥ 1 / 4 * min (sumInv H i / 2) 1 := by
  exact lemmaB_core H i
