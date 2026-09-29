-- Prove2me | solution 1 for NonmonotoneSubmod.SmoothLS.terminal_upper_estimates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:15:15.474492+00:00
-- url     : https://prove2.me/submissions/25df3889-40d5-4af4-ab32-571fc2a2c859

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

open Finset

theorem aux_tue_split {X : Type} [Fintype X] [DecidableEq X] (h : Finset X → ℝ) (x : X → ℝ)
    (a : X) :
    NonmonotoneSubmod.Shared.F h x = ∑ t ∈ (univ.erase a).powerset,
      ((1 - x a) * h t + x a * h (insert a t)) *
        ∏ i ∈ univ.erase a, (if i ∈ t then x i else 1 - x i) := by
  unfold NonmonotoneSubmod.Shared.F
  have hu : (univ : Finset (Finset X)) = (insert a (univ.erase a)).powerset := by
    rw [Finset.insert_erase (mem_univ a), Finset.powerset_univ]
  rw [hu, Finset.sum_powerset_insert (Finset.notMem_erase a _), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hat : a ∉ t := by
    intro hm
    have := (Finset.mem_powerset.mp ht) hm
    simp at this
  have e1 : ∏ i : X, (if i ∈ t then x i else 1 - x i) =
      (1 - x a) * ∏ i ∈ univ.erase a, (if i ∈ t then x i else 1 - x i) := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ a)]
    simp [hat]
  have e2 : ∏ i : X, (if i ∈ insert a t then x i else 1 - x i) =
      x a * ∏ i ∈ univ.erase a, (if i ∈ t then x i else 1 - x i) := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ a)]
    simp only [Finset.mem_insert, true_or, if_true]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hia : i ≠ a := Finset.ne_of_mem_erase hi
    simp [hia]
  rw [e1, e2]
  ring

theorem aux_tue_decomp {X : Type} [Fintype X] [DecidableEq X] (h : Finset X → ℝ) (x : X → ℝ)
    (a : X) :
    NonmonotoneSubmod.Shared.F h x =
      (1 - x a) * NonmonotoneSubmod.Shared.F (fun S => h (S.erase a)) x
      + x a * NonmonotoneSubmod.Shared.F (fun S => h (insert a S)) x := by
  rw [aux_tue_split h x a, aux_tue_split (fun S => h (S.erase a)) x a,
    aux_tue_split (fun S => h (insert a S)) x a, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hat : a ∉ t := by
    intro hm
    have := (Finset.mem_powerset.mp ht) hm
    simp at this
  simp only [Finset.erase_insert hat, Finset.erase_eq_of_notMem hat, Finset.insert_idem]
  ring

theorem aux_tue_F_mono {X : Type} [Fintype X] [DecidableEq X] (g h : Finset X → ℝ)
    (x : X → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hgh : ∀ S, g S ≤ h S) :
    NonmonotoneSubmod.Shared.F g x ≤ NonmonotoneSubmod.Shared.F h x := by
  unfold NonmonotoneSubmod.Shared.F
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_right (hgh S)
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hx i).1
  · linarith [(hx i).2]

theorem aux_tue_F_add_sum {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (D : Finset X) (g : X → Finset X → ℝ) (x : X → ℝ) :
    NonmonotoneSubmod.Shared.F (fun S => f S + ∑ a ∈ D, g a S) x =
      NonmonotoneSubmod.Shared.F f x + ∑ a ∈ D, NonmonotoneSubmod.Shared.F (g a) x := by
  unfold NonmonotoneSubmod.Shared.F
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  exact Finset.sum_comm

theorem aux_tue_F_sub {X : Type} [Fintype X] [DecidableEq X] (g h : Finset X → ℝ)
    (x : X → ℝ) :
    NonmonotoneSubmod.Shared.F (fun S => g S - h S) x =
      NonmonotoneSubmod.Shared.F g x - NonmonotoneSubmod.Shared.F h x := by
  unfold NonmonotoneSubmod.Shared.F
  simp_rw [sub_mul, Finset.sum_sub_distrib]

theorem aux_tue_union {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S D : Finset X) :
    f (S ∪ D) ≤ f S + ∑ a ∈ D, (f (insert a S) - f S) := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a D haD ih =>
    rw [Finset.sum_insert haD]
    by_cases haS : a ∈ S
    · have e : S ∪ insert a D = S ∪ D := by
        ext y
        simp only [mem_union, mem_insert]
        constructor
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Or.inl haS
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      rw [e, Finset.insert_eq_of_mem haS]
      linarith
    · have hsub := hf (insert a S) (S ∪ D)
      have e1 : insert a S ∪ (S ∪ D) = S ∪ insert a D := by
        ext y; simp only [mem_union, mem_insert]; tauto
      have e2 : insert a S ∩ (S ∪ D) = S := by
        ext y
        simp only [mem_inter, mem_insert, mem_union]
        constructor
        · rintro ⟨rfl | h1, h2⟩
          · rcases h2 with h2 | h2
            · exact absurd h2 haS
            · exact absurd h2 haD
          · exact h1
        · intro h
          exact ⟨Or.inr h, Or.inl h⟩
      rw [e1, e2] at hsub
      linarith

theorem aux_tue_sdiff {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S E : Finset X) :
    f (S \ E) ≤ f S + ∑ a ∈ E, (f (S.erase a) - f S) := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert a E haE ih =>
    rw [Finset.sum_insert haE]
    by_cases haS : a ∈ S
    · have hsub := hf (S.erase a) (S \ E)
      have e1 : S.erase a ∪ (S \ E) = S := by
        ext y
        simp only [mem_union, mem_erase, mem_sdiff]
        constructor
        · rintro (h | h)
          · exact h.2
          · exact h.1
        · intro h
          by_cases hya : y = a
          · subst hya
            exact Or.inr ⟨h, haE⟩
          · exact Or.inl ⟨hya, h⟩
      have e2 : S.erase a ∩ (S \ E) = S \ insert a E := by
        ext y; simp only [mem_inter, mem_erase, mem_sdiff, mem_insert]; tauto
      rw [e1, e2] at hsub
      linarith
    · have e : S \ insert a E = S \ E := by
        ext y
        simp only [mem_sdiff, mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h => h2 (Or.inr h)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rintro (rfl | h)
          · exact haS h1
          · exact h2 h
      rw [e, Finset.erase_eq_of_notMem haS]
      linarith

end NonmonotoneSubmod.SmoothLS

open NonmonotoneSubmod.SmoothLS Finset

theorem solution {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A : Finset X) :
    ((∀ x, x ∉ A → omegaB f A (1 / 3) x ≤ 3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) →
      ∀ C : Finset X, NonmonotoneSubmod.Shared.F (fun S => f (S ∪ (Aᶜ ∩ C))) (biasPt A (1 / 3)) ≤
        Phi f (1 / 3) A + 2 / (Fintype.card X : ℝ) * NonmonotoneSubmod.Shared.OPT f) ∧
    ((∀ x, x ∈ A → -(3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ≤ omegaB f A (1 / 3) x) →
      ∀ C : Finset X, NonmonotoneSubmod.Shared.F (fun S => f (S ∩ (Aᶜ ∪ C))) (biasPt A (1 / 3)) ≤
        Phi f (1 / 3) A + 2 / (Fintype.card X : ℝ) * NonmonotoneSubmod.Shared.OPT f) := by
  set n : ℝ := (Fintype.card X : ℝ) with hn
  set O := NonmonotoneSubmod.Shared.OPT f with hO
  set p := biasPt A (1 / 3 : ℝ) with hp
  have hnpos : (0 : ℝ) < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hO0 : 0 ≤ O := le_trans (hf0 ∅) (Finset.le_sup' f (Finset.mem_univ ∅))
  have hp01 : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i; rw [hp]; unfold biasPt; split_ifs <;> constructor <;> norm_num
  have hPhi : Phi f (1 / 3) A = NonmonotoneSubmod.Shared.F f p := rfl
  set K : ℝ := O / n ^ 2 with hK
  have h3 : 3 / n ^ 2 * O = 3 * K := by rw [hK]; ring
  have h2 : 2 / n ^ 2 * O = 2 * K := by rw [hK]; ring
  have hcard : ∀ D : Finset X, (D.card : ℝ) * (2 * K) ≤ 2 / n * O := by
    intro D
    have hD : (D.card : ℝ) ≤ n := by rw [hn]; exact_mod_cast Finset.card_le_univ D
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    calc (D.card : ℝ) * (2 * K) ≤ n * (2 * K) := by
          apply mul_le_mul_of_nonneg_right hD; positivity
      _ = 2 / n * O := by rw [hK]; field_simp
  constructor
  · intro hB C
    set D := Aᶜ ∩ C with hD
    have step1 := aux_tue_F_mono (fun S => f (S ∪ D))
      (fun S => f S + ∑ a ∈ D, (f (insert a S) - f S)) p hp01 (fun S => aux_tue_union f hf S D)
    rw [aux_tue_F_add_sum] at step1
    have hterm : ∀ a ∈ D,
        NonmonotoneSubmod.Shared.F (fun S => f (insert a S) - f S) p ≤ 2 * K := by
      intro a ha
      have haA : a ∉ A := by
        rw [hD] at ha
        simp only [mem_inter, mem_compl] at ha
        exact ha.1
      have hpa : p a = 1 / 3 := by rw [hp]; unfold biasPt; simp only [haA, if_false]; norm_num
      rw [aux_tue_F_sub]
      have hdec := aux_tue_decomp f p a
      have hom := hB a haA
      unfold omegaB at hom
      rw [h3] at hom
      rw [hpa] at hdec
      linarith
    calc _ ≤ _ := step1
      _ ≤ NonmonotoneSubmod.Shared.F f p + ∑ a ∈ D, (2 * K) := by
          gcongr with a ha
          exact hterm a ha
      _ = NonmonotoneSubmod.Shared.F f p + (D.card : ℝ) * (2 * K) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by rw [hPhi]; linarith [hcard D]
  · intro hA C
    set E := A \ C with hE
    have hset : ∀ S : Finset X, S ∩ (Aᶜ ∪ C) = S \ E := by
      intro S
      ext y
      simp only [hE, mem_inter, mem_union, mem_compl, mem_sdiff]
      tauto
    simp_rw [hset]
    have step1 := aux_tue_F_mono (fun S => f (S \ E))
      (fun S => f S + ∑ a ∈ E, (f (S.erase a) - f S)) p hp01 (fun S => aux_tue_sdiff f hf S E)
    rw [aux_tue_F_add_sum] at step1
    have hterm : ∀ a ∈ E,
        NonmonotoneSubmod.Shared.F (fun S => f (S.erase a) - f S) p ≤ 2 * K := by
      intro a ha
      have haA : a ∈ A := by
        rw [hE] at ha
        simp only [mem_sdiff] at ha
        exact ha.1
      have hpa : p a = 2 / 3 := by rw [hp]; unfold biasPt; simp only [haA, if_true]; norm_num
      rw [aux_tue_F_sub]
      have hdec := aux_tue_decomp f p a
      have hom := hA a haA
      unfold omegaB at hom
      rw [h3] at hom
      rw [hpa] at hdec
      linarith
    calc _ ≤ _ := step1
      _ ≤ NonmonotoneSubmod.Shared.F f p + ∑ a ∈ E, (2 * K) := by
          gcongr with a ha
          exact hterm a ha
      _ = NonmonotoneSubmod.Shared.F f p + (E.card : ℝ) * (2 * K) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by rw [hPhi]; linarith [hcard E]
