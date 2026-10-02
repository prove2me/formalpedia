-- Prove2me | solution 1 for NonmonotoneSubmod.QueryLB.hard_instance_submodular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T21:53:24.696281+00:00
-- url     : https://prove2.me/submissions/91fea447-5942-4032-a452-a5c4e808cb5b

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance

set_option autoImplicit false

namespace Paa9bff90
open NonmonotoneSubmod.QueryLB

noncomputable def qq (u : ℝ) : ℝ := (max u 0) ^ 2
noncomputable def rho (m : ℕ) (t : ℝ) : ℝ := qq (t - m) + qq (-t - m)
noncomputable def Phi (n m : ℕ) (k l : ℝ) : ℝ := (k + l) * ((n : ℝ) - k - l) + rho m (k - l)

lemma qq_nonneg (u : ℝ) : 0 ≤ qq u := by unfold qq; positivity

lemma qq_second (u : ℝ) :
    0 ≤ qq (u + 1) + qq (u - 1) - 2 * qq u ∧ qq (u + 1) + qq (u - 1) - 2 * qq u ≤ 2 ∧
      (u ≤ -1 → qq (u + 1) + qq (u - 1) - 2 * qq u = 0) := by
  unfold qq
  rcases le_or_gt u (-1) with h | h
  · have h1 : max (u + 1) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (u - 1) 0 = 0 := max_eq_right (by linarith)
    have h3 : max u 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2, h3]; norm_num
  rcases le_or_gt u 0 with h0 | h0
  · have h1 : max (u + 1) 0 = u + 1 := max_eq_left (by linarith)
    have h2 : max (u - 1) 0 = 0 := max_eq_right (by linarith)
    have h3 : max u 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2, h3]
    refine ⟨by nlinarith, by nlinarith, fun hh => by linarith⟩
  rcases le_or_gt u 1 with h1' | h1'
  · have h1 : max (u + 1) 0 = u + 1 := max_eq_left (by linarith)
    have h2 : max (u - 1) 0 = 0 := max_eq_right (by linarith)
    have h3 : max u 0 = u := max_eq_left (by linarith)
    rw [h1, h2, h3]
    refine ⟨by nlinarith, by nlinarith, fun hh => by linarith⟩
  · have h1 : max (u + 1) 0 = u + 1 := max_eq_left (by linarith)
    have h2 : max (u - 1) 0 = u - 1 := max_eq_left (by linarith)
    have h3 : max u 0 = u := max_eq_left (by linarith)
    rw [h1, h2, h3]
    refine ⟨by nlinarith, by nlinarith, fun hh => by linarith⟩

lemma rho_second (m : ℕ) (hm : 1 ≤ m) (x y z : ℝ) (h1 : y = x + 1) (h2 : z = y + 1) :
    0 ≤ rho m z + rho m x - 2 * rho m y ∧ rho m z + rho m x - 2 * rho m y ≤ 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have e1 : rho m z + rho m x - 2 * rho m y =
      (qq ((y - m) + 1) + qq ((y - m) - 1) - 2 * qq (y - m)) +
      (qq ((-y - m) + 1) + qq ((-y - m) - 1) - 2 * qq (-y - m)) := by
    unfold rho
    have a1 : z - m = (y - m) + 1 := by rw [h2]; ring
    have a2 : x - m = (y - m) - 1 := by rw [h1]; ring
    have a3 : -z - m = (-y - m) - 1 := by rw [h2]; ring
    have a4 : -x - m = (-y - m) + 1 := by rw [h1]; ring
    rw [a1, a2, a3, a4]; ring
  rw [e1]
  obtain ⟨p1, p2, p3⟩ := qq_second (y - m)
  obtain ⟨q1, q2, q3⟩ := qq_second (-y - m)
  by_cases hc : y - m ≤ -1
  · have := p3 hc
    rw [this]; constructor <;> linarith
  · have hc2 : -y - m ≤ -1 := by
      by_contra hh
      push_neg at hh hc
      linarith
    have := q3 hc2
    rw [this]; constructor <;> linarith

lemma rho_even (m : ℕ) (t : ℝ) : rho m (-t) = rho m t := by
  unfold rho
  rw [neg_neg, add_comm]

lemma rho_nonneg (m : ℕ) (t : ℝ) : 0 ≤ rho m t := by
  unfold rho; linarith [qq_nonneg (t - m), qq_nonneg (-t - m)]

lemma fkl_eq (n m k l : ℕ) : fkl n m k l = Phi n m (k : ℝ) (l : ℝ) := by
  unfold fkl Phi rho qq
  by_cases h : |(k : ℝ) - l| ≤ m
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := abs_le.mp h
    have e1 : max ((k : ℝ) - l - m) 0 = 0 := max_eq_right (by linarith)
    have e2 : max (-((k : ℝ) - l) - m) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2]; ring
  · rw [if_neg h]
    push_neg at h
    rcases le_or_gt 0 ((k : ℝ) - l) with h0 | h0
    · rw [abs_of_nonneg h0] at h ⊢
      have e1 : max ((k : ℝ) - l - m) 0 = (k : ℝ) - l - m := max_eq_left (by linarith)
      have e2 : max (-((k : ℝ) - l) - m) 0 = 0 := max_eq_right (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
      rw [e1, e2]; ring
    · rw [abs_of_neg h0] at h ⊢
      have e1 : max ((k : ℝ) - l - m) 0 = 0 := max_eq_right (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
      have e2 : max (-((k : ℝ) - l) - m) 0 = -((k : ℝ) - l) - m := max_eq_left (by linarith)
      rw [e1, e2]; ring

lemma Phi_cc (n m : ℕ) (hm : 1 ≤ m) (k l : ℝ) :
    Phi n m (k + 1 + 1) l + Phi n m k l ≤ Phi n m (k + 1) l + Phi n m (k + 1) l := by
  unfold Phi
  have := (rho_second m hm (k - l) (k + 1 - l) (k + 1 + 1 - l) (by ring) (by ring)).2
  nlinarith

lemma Phi_dd (n m : ℕ) (hm : 1 ≤ m) (k l : ℝ) :
    Phi n m k (l + 1 + 1) + Phi n m k l ≤ Phi n m k (l + 1) + Phi n m k (l + 1) := by
  unfold Phi
  have := (rho_second m hm (k - (l + 1 + 1)) (k - (l + 1)) (k - l) (by ring) (by ring)).2
  nlinarith

lemma Phi_cd (n m : ℕ) (hm : 1 ≤ m) (k l : ℝ) :
    Phi n m (k + 1) (l + 1) + Phi n m k l ≤ Phi n m (k + 1) l + Phi n m k (l + 1) := by
  unfold Phi
  have := (rho_second m hm (k - (l + 1)) (k - l) (k + 1 - l) (by ring) (by ring)).1
  have e : k + 1 - (l + 1) = k - l := by ring
  rw [e]
  nlinarith

/-! general submodularity from diminishing returns of pairs -/

lemma dr_nested {α : Type} [DecidableEq α] (f : Finset α → ℝ)
    (h : ∀ (S : Finset α) (x y : α), x ∉ S → y ∉ S → x ≠ y →
      f (insert x (insert y S)) + f S ≤ f (insert x S) + f (insert y S)) :
    ∀ (D A : Finset α) (x : α), x ∉ A → x ∉ D → Disjoint A D →
      f (insert x (A ∪ D)) - f (A ∪ D) ≤ f (insert x A) - f A := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro A x _ _ _; simp
  | insert d D' hd ih =>
    intro A x hxA hxD hdisj
    have hdA : d ∉ A := by
      intro hh
      exact Finset.disjoint_left.mp hdisj hh (Finset.mem_insert_self d D')
    have hdisj' : Disjoint A D' := by
      refine Finset.disjoint_left.mpr (fun a ha haD => ?_)
      exact Finset.disjoint_left.mp hdisj ha (Finset.mem_insert_of_mem haD)
    have hxd : x ≠ d := by
      intro hh; apply hxD; rw [hh]; exact Finset.mem_insert_self d D'
    have hxD' : x ∉ D' := fun hh => hxD (Finset.mem_insert_of_mem hh)
    have hdB : d ∉ A ∪ D' := by
      intro hh; rcases Finset.mem_union.mp hh with h1 | h1
      · exact hdA h1
      · exact hd h1
    have hxB : x ∉ A ∪ D' := by
      intro hh; rcases Finset.mem_union.mp hh with h1 | h1
      · exact hxA h1
      · exact hxD' h1
    have h1 := h (A ∪ D') x d hxB hdB hxd
    have h2 := ih A x hxA hxD' hdisj'
    rw [Finset.union_insert]
    linarith

lemma dr_sub {α : Type} [DecidableEq α] (f : Finset α → ℝ)
    (h : ∀ (S : Finset α) (x y : α), x ∉ S → y ∉ S → x ≠ y →
      f (insert x (insert y S)) + f S ≤ f (insert x S) + f (insert y S))
    (A B : Finset α) (x : α) (hAB : A ⊆ B) (hxB : x ∉ B) :
    f (insert x B) - f B ≤ f (insert x A) - f A := by
  have := dr_nested f h (B \ A) A x (fun hh => hxB (hAB hh))
    (fun hh => hxB (Finset.mem_sdiff.mp hh).1) Finset.disjoint_sdiff
  rwa [Finset.union_sdiff_of_subset hAB] at this

lemma submod_of_dr {α : Type} [DecidableEq α] (f : Finset α → ℝ)
    (h : ∀ (S : Finset α) (x y : α), x ∉ S → y ∉ S → x ≠ y →
      f (insert x (insert y S)) + f S ≤ f (insert x S) + f (insert y S))
    (S T : Finset α) : f (S ∪ T) + f (S ∩ T) ≤ f S + f T := by
  have key : ∀ (D : Finset α) (A S : Finset α), A ⊆ S → Disjoint S D →
      f (S ∪ D) - f S ≤ f (A ∪ D) - f A := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro A S _ _; simp
    | insert d D' hd ih =>
      intro A S hAS hdisj
      have hdS : d ∉ S := by
        intro hh
        exact Finset.disjoint_left.mp hdisj hh (Finset.mem_insert_self d D')
      have hdisj' : Disjoint S D' := by
        refine Finset.disjoint_left.mpr (fun a ha haD => ?_)
        exact Finset.disjoint_left.mp hdisj ha (Finset.mem_insert_of_mem haD)
      have hdB : d ∉ S ∪ D' := by
        intro hh; rcases Finset.mem_union.mp hh with h1 | h1
        · exact hdS h1
        · exact hd h1
      have hsub : A ∪ D' ⊆ S ∪ D' := Finset.union_subset_union hAS (Finset.Subset.refl _)
      have h1 := dr_sub f h _ _ d hsub hdB
      have h2 := ih A S hAS hdisj'
      rw [Finset.union_insert, Finset.union_insert]
      linarith
  have := key (T \ S) (S ∩ T) S Finset.inter_subset_left Finset.disjoint_sdiff
  have e1 : S ∪ (T \ S) = S ∪ T := by
    ext a; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have e2 : S ∩ T ∪ (T \ S) = T := by
    ext a; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [e1, e2] at this
  linarith


/-! ## facts about `fC` -/

lemma fC_eq (n m : ℕ) (C S : Finset (Fin n)) :
    fC n m C S = Phi n m ((S ∩ C).card : ℝ) ((S ∩ Cᶜ).card : ℝ) := by
  unfold fC; exact fkl_eq n m _ _

lemma card_ins {n : ℕ} (C S : Finset (Fin n)) (x : Fin n) (hx : x ∉ S) :
    (((insert x S) ∩ C).card : ℝ) = ((S ∩ C).card : ℝ) + (if x ∈ C then 1 else 0) ∧
    (((insert x S) ∩ Cᶜ).card : ℝ) = ((S ∩ Cᶜ).card : ℝ) + (if x ∈ C then 0 else 1) := by
  by_cases hxC : x ∈ C
  · have hxnot : x ∉ Cᶜ := by simpa using hxC
    rw [Finset.insert_inter_of_mem hxC, Finset.insert_inter_of_notMem hxnot,
      Finset.card_insert_of_notMem (fun h => hx (Finset.mem_inter.mp h).1)]
    simp [hxC]
  · have hxc : x ∈ Cᶜ := by simpa using hxC
    rw [Finset.insert_inter_of_notMem hxC, Finset.insert_inter_of_mem hxc,
      Finset.card_insert_of_notMem (fun h => hx (Finset.mem_inter.mp h).1)]
    simp [hxC]

lemma fC_dr (n m : ℕ) (hm : 1 ≤ m) (C : Finset (Fin n)) :
    ∀ (S : Finset (Fin n)) (x y : Fin n), x ∉ S → y ∉ S → x ≠ y →
      fC n m C (insert x (insert y S)) + fC n m C S ≤ fC n m C (insert x S) + fC n m C (insert y S) := by
  intro S x y hx hy hxy
  have hx' : x ∉ insert y S := by
    simp only [Finset.mem_insert, not_or]; exact ⟨hxy, hx⟩
  have h1 := card_ins C (insert y S) x hx'
  have h2 := card_ins C S y hy
  have h3 := card_ins C S x hx
  rw [fC_eq, fC_eq, fC_eq, fC_eq, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  by_cases hxC : x ∈ C <;> by_cases hyC : y ∈ C
  · simp only [hxC, hyC, if_true, if_false, add_zero]
    exact Phi_cc n m hm _ _
  · simp only [hxC, hyC, if_true, if_false, add_zero]
    exact Phi_cd n m hm _ _
  · simp only [hxC, hyC, if_true, if_false, add_zero]
    have := Phi_cd n m hm (((S ∩ C).card : ℝ)) (((S ∩ Cᶜ).card : ℝ))
    linarith
  · simp only [hxC, hyC, if_true, if_false, add_zero]
    exact Phi_dd n m hm _ _

lemma fC_submod (n m : ℕ) (hm : 1 ≤ m) (C : Finset (Fin n)) :
    NonmonotoneSubmod.Shared.Submodular (fC n m C) := by
  intro S T
  exact submod_of_dr (fC n m C) (fC_dr n m hm C) S T

end Paa9bff90

open NonmonotoneSubmod.QueryLB in
theorem solution (n m : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (C : Finset (Fin n)) (hC : C.card = n / 2) :
    NonmonotoneSubmod.Shared.Submodular (fC n m C) := by
  exact Paa9bff90.fC_submod n m hm C
