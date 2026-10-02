-- Prove2me | solution 1 for NonmonotoneSubmod.QueryLB.deterministic_average_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:28:42.717047+00:00
-- url     : https://prove2.me/submissions/de5cda7e-1c37-4bf6-aea8-5d23f48328f1

import Mathlib
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance
import Definitions.Def_NonmonotoneSubmod_QueryLB_QueryAlgorithm

set_option autoImplicit false

namespace Pdcc79144
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

lemma cardsum {n : ℕ} (C S : Finset (Fin n)) :
    ((S ∩ C).card : ℝ) + ((S ∩ Cᶜ).card : ℝ) = (S.card : ℝ) := by
  have e : S ∩ Cᶜ = S \ C := by ext; simp
  have := Finset.card_sdiff_add_card_inter S C
  rw [e]
  exact_mod_cast (by omega : (S ∩ C).card + (S \ C).card = S.card)

lemma card_le_n {n : ℕ} (S : Finset (Fin n)) : (S.card : ℝ) ≤ n := by
  have := Finset.card_le_univ S
  simp only [Fintype.card_fin] at this
  exact_mod_cast this

lemma fC_eq (n m : ℕ) (C S : Finset (Fin n)) :
    fC n m C S = Phi n m ((S ∩ C).card : ℝ) ((S ∩ Cᶜ).card : ℝ) := by
  unfold fC; exact fkl_eq n m _ _

lemma fC_nonneg (n m : ℕ) (C S : Finset (Fin n)) : 0 ≤ fC n m C S := by
  rw [fC_eq]
  unfold Phi
  have h1 := cardsum C S
  have h2 := card_le_n S
  have h3 : (0:ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have h4 : ((S ∩ C).card : ℝ) + ((S ∩ Cᶜ).card : ℝ) = (S.card : ℝ) := h1
  have : ((S ∩ C).card : ℝ) + ((S ∩ Cᶜ).card : ℝ) * 1 = (S.card : ℝ) := by rw [mul_one]; exact h1
  have e : (((S ∩ C).card : ℝ) + ((S ∩ Cᶜ).card : ℝ)) * ((n : ℝ) - ((S ∩ C).card : ℝ) - ((S ∩ Cᶜ).card : ℝ))
      = (S.card : ℝ) * ((n : ℝ) - S.card) := by
    rw [← h4]; ring
  rw [e]
  have := rho_nonneg m (((S ∩ C).card : ℝ) - ((S ∩ Cᶜ).card : ℝ))
  have := mul_nonneg h3 (sub_nonneg.mpr h2)
  linarith

lemma fC_symm (n m N : ℕ) (hn : n = N + N) (C : Finset (Fin n)) (hC : C.card = N)
    (S : Finset (Fin n)) : fC n m C Sᶜ = fC n m C S := by
  rw [fC_eq, fC_eq]
  have e1 : Sᶜ ∩ C = C \ S := by ext; simp; tauto
  have e2 : Sᶜ ∩ Cᶜ = Cᶜ \ S := by ext; simp; tauto
  have e3 : C ∩ S = S ∩ C := Finset.inter_comm _ _
  have e4 : Cᶜ ∩ S = S ∩ Cᶜ := Finset.inter_comm _ _
  have hCc : (Cᶜ).card = N := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  have h1 := Finset.card_sdiff_add_card_inter C S
  have h2 := Finset.card_sdiff_add_card_inter Cᶜ S
  rw [e3] at h1
  rw [e4] at h2
  rw [e1, e2]
  have r1 : ((C \ S).card : ℝ) = (N : ℝ) - ((S ∩ C).card : ℝ) := by
    have : (C \ S).card + (S ∩ C).card = N := by omega
    have := congrArg (fun z : ℕ => (z : ℝ)) this
    simp only [Nat.cast_add] at this
    linarith
  have r2 : ((Cᶜ \ S).card : ℝ) = (N : ℝ) - ((S ∩ Cᶜ).card : ℝ) := by
    have : (Cᶜ \ S).card + (S ∩ Cᶜ).card = N := by omega
    have := congrArg (fun z : ℕ => (z : ℝ)) this
    simp only [Nat.cast_add] at this
    linarith
  rw [r1, r2]
  unfold Phi
  have hn' : (n : ℝ) = N + N := by exact_mod_cast hn
  have e5 : ((N : ℝ) - ((S ∩ C).card : ℝ)) - ((N : ℝ) - ((S ∩ Cᶜ).card : ℝ))
      = -(((S ∩ C).card : ℝ) - ((S ∩ Cᶜ).card : ℝ)) := by ring
  rw [e5, rho_even, hn']
  ring

lemma rho_le (m : ℕ) (Nr d : ℝ) (hmN : (m : ℝ) ≤ Nr) (hd : |d| ≤ Nr) :
    rho m d ≤ (Nr - m) ^ 2 := by
  unfold rho qq
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases le_or_gt 0 d with h0 | h0
  · have e2 : max (-d - m) 0 = 0 := max_eq_right (by linarith)
    rw [e2]
    have h1 : max (d - m) 0 ≤ Nr - m := max_le (by linarith) (by linarith)
    have h2 : (0:ℝ) ≤ max (d - m) 0 := le_max_right _ _
    have := sq_le_sq' (by linarith : -(Nr - m) ≤ max (d - m) 0) h1
    nlinarith
  · have e2 : max (d - m) 0 = 0 := max_eq_right (by linarith)
    rw [e2]
    have h1 : max (-d - m) 0 ≤ Nr - m := max_le (by linarith) (by linarith)
    have h2 : (0:ℝ) ≤ max (-d - m) 0 := le_max_right _ _
    have := sq_le_sq' (by linarith : -(Nr - m) ≤ max (-d - m) 0) h1
    nlinarith

lemma fC_le (n m N : ℕ) (hn : n = N + N) (hmn : 2 * m ≤ n) (C : Finset (Fin n)) (hC : C.card = N)
    (S : Finset (Fin n)) :
    fC n m C S ≤ (n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2 := by
  rw [fC_eq]
  have hCc : (Cᶜ).card = N := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  have ha : (S ∩ C).card ≤ N := by
    rw [← hC]; exact Finset.card_le_card Finset.inter_subset_right
  have hb : (S ∩ Cᶜ).card ≤ N := by
    rw [← hCc]; exact Finset.card_le_card Finset.inter_subset_right
  have ha' : ((S ∩ C).card : ℝ) ≤ N := by exact_mod_cast ha
  have hb' : ((S ∩ Cᶜ).card : ℝ) ≤ N := by exact_mod_cast hb
  have ha0 : (0 : ℝ) ≤ ((S ∩ C).card : ℝ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ ((S ∩ Cᶜ).card : ℝ) := Nat.cast_nonneg _
  have hmN : (m : ℝ) ≤ N := by
    have : m ≤ N := by omega
    exact_mod_cast this
  have hn' : (n : ℝ) = N + N := by exact_mod_cast hn
  have hr := rho_le m (N : ℝ) (((S ∩ C).card : ℝ) - ((S ∩ Cᶜ).card : ℝ)) hmN
    (abs_le.mpr ⟨by linarith, by linarith⟩)
  unfold Phi
  set a : ℝ := ((S ∩ C).card : ℝ)
  set b : ℝ := ((S ∩ Cᶜ).card : ℝ)
  have hg : (a + b) * ((n : ℝ) - a - b) ≤ (n : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg (a + b - (n : ℝ) / 2)]
  rw [hn'] at hg ⊢
  nlinarith

lemma fC_at_C (n m N : ℕ) (hn : n = N + N) (hmn : 2 * m ≤ n) (C : Finset (Fin n)) (hC : C.card = N) :
    fC n m C C = (n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2 := by
  rw [fC_eq]
  have e1 : C ∩ C = C := Finset.inter_self C
  have e2 : C ∩ Cᶜ = ∅ := Finset.inter_compl C
  rw [e1, e2, hC]
  have hmN : (m : ℝ) ≤ N := by
    have : m ≤ N := by omega
    exact_mod_cast this
  have hn' : (n : ℝ) = N + N := by exact_mod_cast hn
  unfold Phi rho qq
  have h1 : max ((N : ℝ) - 0 - m) 0 = (N : ℝ) - m := by
    rw [sub_zero]; exact max_eq_left (by linarith)
  have h2 : max (-((N : ℝ) - 0) - m) 0 = 0 := by
    rw [sub_zero]; exact max_eq_right (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m), (Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  simp only [Finset.card_empty, Nat.cast_zero]
  rw [h1, h2, hn']
  ring

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

lemma balanced_eq (n m : ℕ) (C Q : Finset (Fin n)) (h : Balanced n m C Q) :
    fC n m C Q = gCut n Q := by
  rw [fC_eq]
  unfold Phi gCut
  have hc := cardsum C Q
  have hr : rho m (((Q ∩ C).card : ℝ) - ((Q ∩ Cᶜ).card : ℝ)) = 0 := by
    unfold rho qq
    have h' := abs_le.mp h
    have e1 : max (((Q ∩ C).card : ℝ) - ((Q ∩ Cᶜ).card : ℝ) - m) 0 = 0 :=
      max_eq_right (by linarith [h'.2])
    have e2 : max (-(((Q ∩ C).card : ℝ) - ((Q ∩ Cᶜ).card : ℝ)) - m) 0 = 0 :=
      max_eq_right (by linarith [h'.1])
    rw [e1, e2]; norm_num
  rw [hr, ← hc]; ring

lemma gCut_le (n : ℕ) (Q : Finset (Fin n)) : gCut n Q ≤ (n : ℝ) ^ 2 / 4 := by
  unfold gCut
  nlinarith [sq_nonneg ((Q.card : ℝ) - (n : ℝ) / 2)]

/-! ## the pairing construction of random balanced sets -/

def pidx (n N : ℕ) (hn : n = N + N) (x : Fin n) : Fin N :=
  ⟨x.val / 2, by have := x.isLt; omega⟩

def evx (n N : ℕ) (hn : n = N + N) (p : Fin N) : Fin n :=
  ⟨2 * p.val, by have := p.isLt; omega⟩

def odx (n N : ℕ) (hn : n = N + N) (p : Fin N) : Fin n :=
  ⟨2 * p.val + 1, by have := p.isLt; omega⟩

lemma pidx_ev (n N : ℕ) (hn : n = N + N) (p : Fin N) : pidx n N hn (evx n N hn p) = p :=
  Fin.ext (by simp only [pidx, evx]; omega)

lemma pidx_od (n N : ℕ) (hn : n = N + N) (p : Fin N) : pidx n N hn (odx n N hn p) = p :=
  Fin.ext (by simp only [pidx, odx]; omega)

def Csig (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) : Finset (Fin n) :=
  Finset.univ.image (fun p : Fin N => if σ p then evx n N hn p else odx n N hn p)

lemma Csig_card (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) : (Csig n N hn σ).card = N := by
  unfold Csig
  rw [Finset.card_image_of_injective]
  · simp
  · have key : ∀ p : Fin N, pidx n N hn (if σ p then evx n N hn p else odx n N hn p) = p := by
      intro p; split_ifs
      · exact pidx_ev n N hn p
      · exact pidx_od n N hn p
    intro p p' h
    exact (key p).symm.trans ((congrArg (pidx n N hn) h).trans (key p'))

lemma mem_Csig (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (x : Fin n) :
    x ∈ Csig n N hn σ ↔ (σ (pidx n N hn x) = true ↔ x.val % 2 = 0) := by
  unfold Csig
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, rfl⟩
    by_cases hp : σ p = true
    · rw [if_pos hp, pidx_ev]
      simp only [evx]
      constructor
      · intro _; omega
      · intro _; exact hp
    · rw [if_neg hp, pidx_od]
      simp only [odx]
      constructor
      · intro h; exact absurd h hp
      · intro h; omega
  · intro h
    refine ⟨pidx n N hn x, ?_⟩
    by_cases hp : σ (pidx n N hn x) = true
    · simp only [hp, if_true]
      have := h.mp hp
      apply Fin.ext; simp only [evx, pidx]; omega
    · have hp0 : ¬ x.val % 2 = 0 := fun hh => hp (h.mpr hh)
      simp only [hp, Bool.false_eq_true, if_false]
      apply Fin.ext; simp only [odx, pidx]; omega

noncomputable def sgn (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (x : Fin n) : ℝ :=
  if x ∈ Csig n N hn σ then 1 else -1

def eps (b : Bool) : ℝ := if b then 1 else -1

def tau {n : ℕ} (x : Fin n) : ℝ := if x.val % 2 = 0 then 1 else -1

def cc (n N : ℕ) (hn : n = N + N) (Q : Finset (Fin n)) (p : Fin N) : ℝ :=
  (if evx n N hn p ∈ Q then 1 else 0) - (if odx n N hn p ∈ Q then 1 else 0)

lemma cc_abs (n N : ℕ) (hn : n = N + N) (Q : Finset (Fin n)) (p : Fin N) :
    |cc n N hn Q p| ≤ 1 := by
  unfold cc
  by_cases h1 : evx n N hn p ∈ Q <;> by_cases h2 : odx n N hn p ∈ Q <;> simp [h1, h2]

lemma diff_eq (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (Q : Finset (Fin n)) :
    ((Q ∩ Csig n N hn σ).card : ℝ) - ((Q ∩ (Csig n N hn σ)ᶜ).card : ℝ)
      = ∑ x ∈ Q, sgn n N hn σ x := by
  induction Q using Finset.induction_on with
  | empty => simp
  | insert x Q hx ih =>
    have h := card_ins (Csig n N hn σ) Q x hx
    rw [h.1, h.2, Finset.sum_insert hx, ← ih]
    unfold sgn
    by_cases hxC : x ∈ Csig n N hn σ <;> simp [hxC] <;> ring

lemma sgn_eq (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (x : Fin n) :
    sgn n N hn σ x = eps (σ (pidx n N hn x)) * tau x := by
  unfold sgn eps tau
  simp only [mem_Csig]
  cases hb : σ (pidx n N hn x) <;> by_cases hp : x.val % 2 = 0 <;> simp [hp]

lemma fiber_eq (n N : ℕ) (hn : n = N + N) (Q : Finset (Fin n)) (p : Fin N) :
    ∑ x ∈ Q.filter (fun x => pidx n N hn x = p), tau x = cc n N hn Q p := by
  have hne : evx n N hn p ≠ odx n N hn p := by
    intro h
    have := congrArg Fin.val h
    simp only [evx, odx] at this
    omega
  have hset : Q.filter (fun x => pidx n N hn x = p)
      = ({evx n N hn p, odx n N hn p} : Finset (Fin n)).filter (fun x => x ∈ Q) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxQ, hx⟩
      refine ⟨?_, hxQ⟩
      have := congrArg Fin.val hx
      simp only [pidx] at this
      by_cases hpar : x.val % 2 = 0
      · left; apply Fin.ext; simp only [evx]; omega
      · right; apply Fin.ext; simp only [odx]; omega
    · rintro ⟨hx, hxQ⟩
      refine ⟨hxQ, ?_⟩
      rcases hx with rfl | rfl
      · exact pidx_ev n N hn p
      · exact pidx_od n N hn p
  rw [hset, Finset.sum_filter, Finset.sum_pair hne]
  unfold cc tau
  have e1 : (evx n N hn p).val % 2 = 0 := by simp only [evx]; omega
  have e2 : ¬ (odx n N hn p).val % 2 = 0 := by simp only [odx]; omega
  simp only [e1, e2, if_true, if_false]
  by_cases h1 : evx n N hn p ∈ Q <;> by_cases h2 : odx n N hn p ∈ Q <;> simp [h1, h2]

lemma D_eq (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (Q : Finset (Fin n)) :
    ((Q ∩ Csig n N hn σ).card : ℝ) - ((Q ∩ (Csig n N hn σ)ᶜ).card : ℝ)
      = ∑ p : Fin N, eps (σ p) * cc n N hn Q p := by
  rw [diff_eq]
  simp_rw [sgn_eq]
  rw [← Finset.sum_fiberwise Q (pidx n N hn)]
  apply Finset.sum_congr rfl
  intro p _
  have : ∀ x ∈ Q.filter (fun x => pidx n N hn x = p),
      eps (σ (pidx n N hn x)) * tau x = eps (σ p) * tau x := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, fiber_eq]

/-! ## Hoeffding-type count over sign vectors -/

lemma hoeff_sum (N : ℕ) (c : Fin N → ℝ) (hc : ∀ p, |c p| ≤ 1) (t : ℝ) :
    ∑ σ : Fin N → Bool, Real.exp (t * ∑ p, eps (σ p) * c p)
      ≤ 2 ^ N * Real.exp (N * t ^ 2 / 2) := by
  have h1 : ∀ σ : Fin N → Bool, Real.exp (t * ∑ p, eps (σ p) * c p)
      = ∏ p, Real.exp (t * (eps (σ p) * c p)) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  have key : ∑ σ : Fin N → Bool, ∏ p, Real.exp (t * (eps (σ p) * c p))
      = ∏ p, ∑ b : Bool, Real.exp (t * (eps b * c p)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [key]
  have h2 : ∀ p : Fin N, ∑ b : Bool, Real.exp (t * (eps b * c p)) ≤ 2 * Real.exp (t ^ 2 / 2) := by
    intro p
    rw [Fintype.sum_bool]
    simp only [eps, if_true, if_false, Bool.false_eq_true]
    have hcosh := Real.cosh_le_exp_half_sq (t * c p)
    rw [Real.cosh_eq] at hcosh
    have hc2 : (t * c p) ^ 2 ≤ t ^ 2 := by
      have : (c p) ^ 2 ≤ 1 := by
        have := hc p
        nlinarith [abs_nonneg (c p), sq_abs (c p)]
      nlinarith [sq_nonneg t]
    have hexp : Real.exp ((t * c p) ^ 2 / 2) ≤ Real.exp (t ^ 2 / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have e1 : t * (1 * c p) = t * c p := by ring
    have e2 : t * (-1 * c p) = -(t * c p) := by ring
    rw [e1, e2]
    linarith
  calc ∏ p, ∑ b : Bool, Real.exp (t * (eps b * c p))
      ≤ ∏ _p : Fin N, (2 * Real.exp (t ^ 2 / 2)) :=
        Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun b _ => (Real.exp_pos _).le))
          (fun p _ => h2 p)
    _ = 2 ^ N * Real.exp (N * t ^ 2 / 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring

lemma tail_sum (N : ℕ) (hN : 0 < N) (c : Fin N → ℝ) (hc : ∀ p, |c p| ≤ 1) (m : ℝ) (hm : 0 ≤ m) :
    ∑ σ : Fin N → Bool, (if m < ∑ p, eps (σ p) * c p then (1 : ℝ) else 0)
      ≤ 2 ^ N * Real.exp (-(m ^ 2) / (2 * N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set t : ℝ := m / N with ht
  have ht0 : 0 ≤ t := div_nonneg hm hNr.le
  have step : ∀ σ : Fin N → Bool, (if m < ∑ p, eps (σ p) * c p then (1 : ℝ) else 0)
      ≤ Real.exp (-(t * m)) * Real.exp (t * ∑ p, eps (σ p) * c p) := by
    intro σ
    rw [← Real.exp_add]
    split_ifs with h
    · rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ t * (∑ p, eps (σ p) * c p - m) := mul_nonneg ht0 (by linarith)
      nlinarith
    · exact (Real.exp_pos _).le
  calc ∑ σ : Fin N → Bool, (if m < ∑ p, eps (σ p) * c p then (1 : ℝ) else 0)
      ≤ ∑ σ : Fin N → Bool, Real.exp (-(t * m)) * Real.exp (t * ∑ p, eps (σ p) * c p) :=
        Finset.sum_le_sum (fun σ _ => step σ)
    _ = Real.exp (-(t * m)) * ∑ σ : Fin N → Bool, Real.exp (t * ∑ p, eps (σ p) * c p) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(t * m)) * (2 ^ N * Real.exp (N * t ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (hoeff_sum N c hc t) (Real.exp_pos _).le
    _ = 2 ^ N * Real.exp (-(m ^ 2) / (2 * N)) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        rw [ht]
        field_simp
        ring

lemma bad_sum (n N m : ℕ) (hn : n = N + N) (hN : 0 < N) (Q : Finset (Fin n)) :
    ∑ σ : Fin N → Bool, (if Balanced n m (Csig n N hn σ) Q then (0 : ℝ) else 1)
      ≤ 2 * (2 ^ N * Real.exp (-((m : ℝ) ^ 2) / (2 * N))) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have t1 := tail_sum N hN (cc n N hn Q) (cc_abs n N hn Q) m hm0
  have t2 := tail_sum N hN (fun p => - cc n N hn Q p) (fun p => by rw [abs_neg]; exact cc_abs n N hn Q p) m hm0
  have pt : ∀ σ : Fin N → Bool, (if Balanced n m (Csig n N hn σ) Q then (0 : ℝ) else 1)
      ≤ (if (m : ℝ) < ∑ p, eps (σ p) * cc n N hn Q p then (1 : ℝ) else 0)
        + (if (m : ℝ) < ∑ p, eps (σ p) * (- cc n N hn Q p) then (1 : ℝ) else 0) := by
    intro σ
    have hD := D_eq n N hn σ Q
    have hneg : ∑ p, eps (σ p) * (- cc n N hn Q p) = -∑ p, eps (σ p) * cc n N hn Q p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [hneg]
    have hbal : Balanced n m (Csig n N hn σ) Q ↔ |∑ p, eps (σ p) * cc n N hn Q p| ≤ m := by
      unfold NonmonotoneSubmod.QueryLB.Balanced
      rw [hD]
    by_cases h1 : (m : ℝ) < ∑ p, eps (σ p) * cc n N hn Q p
    · have : ¬ Balanced n m (Csig n N hn σ) Q := by
        rw [hbal]; push_neg; exact lt_of_lt_of_le h1 (le_abs_self _)
      simp only [this, h1, if_true, if_false]
      split_ifs <;> norm_num
    · by_cases h2 : (m : ℝ) < -∑ p, eps (σ p) * cc n N hn Q p
      · simp only [h1, h2, if_true, if_false]
        split_ifs <;> norm_num
      · have : Balanced n m (Csig n N hn σ) Q := by
          rw [hbal, abs_le]; push_neg at h1 h2; constructor <;> linarith
        simp only [this, if_true]
        have e1 : (0:ℝ) ≤ (if (m : ℝ) < ∑ p, eps (σ p) * cc n N hn Q p then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        have e2 : (0:ℝ) ≤ (if (m : ℝ) < -∑ p, eps (σ p) * cc n N hn Q p then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        linarith
  calc ∑ σ : Fin N → Bool, (if Balanced n m (Csig n N hn σ) Q then (0 : ℝ) else 1)
      ≤ ∑ σ : Fin N → Bool, ((if (m : ℝ) < ∑ p, eps (σ p) * cc n N hn Q p then (1 : ℝ) else 0)
        + (if (m : ℝ) < ∑ p, eps (σ p) * (- cc n N hn Q p) then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun σ _ => pt σ)
    _ = _ := Finset.sum_add_distrib
    _ ≤ 2 * (2 ^ N * Real.exp (-((m : ℝ) ^ 2) / (2 * N))) := by linarith

/-! ## the adaptive argument -/

lemma answers_eq {n q : ℕ} (A : DetAlg (Fin n) q) (h1 h2 : Finset (Fin n) → ℝ) (i : ℕ)
    (H : ∀ j < i, h1 (A.queryAt h2 j) = h2 (A.queryAt h2 j)) :
    A.answers h1 i = A.answers h2 i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have e := ih (fun j hj => H j (Nat.lt_succ_of_lt hj))
    have hi := H i (Nat.lt_succ_self i)
    unfold DetAlg.queryAt at hi
    simp only [DetAlg.answers]
    rw [e, hi]


lemma numeric (x : ℝ) (hx : 0 ≤ x) (q : ℕ) (hq : (q : ℝ) < Real.exp (x / 8)) :
    ((q : ℝ) + 1) * (2 * Real.exp (-x)) ≤ 2 * Real.exp (-(x / 8)) + 2 * Real.exp (-(x / 4)) := by
  have h1 : Real.exp (-x) ≤ Real.exp (-(x / 4)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (x / 8) * Real.exp (-x) ≤ Real.exp (-(x / 8)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have h3 : (q : ℝ) * Real.exp (-x) ≤ Real.exp (x / 8) * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right hq.le (Real.exp_pos _).le
  nlinarith


/-! ## uniform n/2-subsets via permutation averaging -/

lemma bal_map (n m : ℕ) (π : Equiv.Perm (Fin n)) (C Q : Finset (Fin n)) :
    Balanced n m (C.map π.toEmbedding) Q ↔ Balanced n m C (Q.map π.symm.toEmbedding) := by
  unfold NonmonotoneSubmod.QueryLB.Balanced
  have h1 : (Q ∩ C.map π.toEmbedding).card = (Q.map π.symm.toEmbedding ∩ C).card := by
    rw [← Finset.card_map π.symm.toEmbedding, Finset.map_inter]
    congr 2
    ext x; simp
  have h2 : (Q ∩ (C.map π.toEmbedding)ᶜ).card = (Q.map π.symm.toEmbedding ∩ Cᶜ).card := by
    rw [← Finset.card_map π.symm.toEmbedding, Finset.map_inter]
    congr 2
    ext x; simp
  rw [h1, h2]

lemma sum_map_P (n N : ℕ) (π : Equiv.Perm (Fin n)) (f : Finset (Fin n) → ℝ) :
    ∑ C ∈ (Finset.univ : Finset (Fin n)).powersetCard N, f (C.map π.toEmbedding)
      = ∑ C ∈ (Finset.univ : Finset (Fin n)).powersetCard N, f C := by
  refine Finset.sum_nbij' (fun C => C.map π.toEmbedding) (fun C => C.map π.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro C hC
    rw [Finset.mem_powersetCard] at hC ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map]; exact hC.2⟩
  · intro C hC
    rw [Finset.mem_powersetCard] at hC ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map]; exact hC.2⟩
  · intro C _
    ext x; simp
  · intro C _
    ext x; simp
  · intro C _; rfl

noncomputable def FF (n m : ℕ) (Q C : Finset (Fin n)) : ℝ :=
  ∑ π : Equiv.Perm (Fin n), (if Balanced n m (C.map π.toEmbedding) Q then (0 : ℝ) else 1)

lemma FF_const (n m : ℕ) (Q C C' : Finset (Fin n)) (h : C'.card = C.card) :
    FF n m Q C = FF n m Q C' := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq C' C h
  unfold FF
  rw [← hτ]
  have e : ∀ π : Equiv.Perm (Fin n),
      (C'.map τ.toEmbedding).map π.toEmbedding = C'.map (π * τ).toEmbedding := by
    intro π
    rw [Finset.map_map]
    congr 1
  simp_rw [e]
  exact Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun π => rfl)

lemma count_bad (n N m : ℕ) (hn : n = N + N) (hN : 0 < N) (Q : Finset (Fin n)) :
    ∑ C ∈ (Finset.univ : Finset (Fin n)).powersetCard N,
        (if Balanced n m C Q then (0 : ℝ) else 1)
      ≤ (((Finset.univ : Finset (Fin n)).powersetCard N).card : ℝ)
          * (2 * Real.exp (-((m : ℝ) ^ 2) / (2 * N))) := by
  classical
  set P := (Finset.univ : Finset (Fin n)).powersetCard N with hP
  set e := Real.exp (-((m : ℝ) ^ 2) / (2 * N)) with he
  set C0 := Csig n N hn (fun _ => true) with hC0
  have hC0c : C0.card = N := Csig_card n N hn _
  have hfact : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hcardperm : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  -- (A) double count over P
  have hA : ∑ C ∈ P, FF n m Q C
      = (Nat.factorial n : ℝ) * ∑ C ∈ P, (if Balanced n m C Q then (0 : ℝ) else 1) := by
    unfold FF
    rw [Finset.sum_comm]
    have : ∀ π : Equiv.Perm (Fin n),
        ∑ C ∈ P, (if Balanced n m (C.map π.toEmbedding) Q then (0 : ℝ) else 1)
          = ∑ C ∈ P, (if Balanced n m C Q then (0 : ℝ) else 1) :=
      fun π => sum_map_P n N π (fun C => if Balanced n m C Q then (0 : ℝ) else 1)
    rw [Finset.sum_congr rfl (fun π _ => this π), Finset.sum_const, hcardperm, nsmul_eq_mul]
  have hB : ∑ C ∈ P, FF n m Q C = (P.card : ℝ) * FF n m Q C0 := by
    rw [Finset.sum_congr rfl (fun C hC => FF_const n m Q C C0 (by
      rw [hC0c]; exact ((Finset.mem_powersetCard.mp hC).2).symm)), Finset.sum_const, nsmul_eq_mul]
  -- (C) average over sigma
  have hC : ∑ σ : Fin N → Bool, FF n m Q (Csig n N hn σ) = (2 : ℝ) ^ N * FF n m Q C0 := by
    rw [Finset.sum_congr rfl (fun σ _ => FF_const n m Q (Csig n N hn σ) C0 (by
      rw [hC0c, Csig_card])), Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hD : ∑ σ : Fin N → Bool, FF n m Q (Csig n N hn σ)
      ≤ (Nat.factorial n : ℝ) * (2 * (2 ^ N * e)) := by
    unfold FF
    rw [Finset.sum_comm]
    have : ∀ π : Equiv.Perm (Fin n),
        ∑ σ : Fin N → Bool,
            (if Balanced n m ((Csig n N hn σ).map π.toEmbedding) Q then (0 : ℝ) else 1)
          ≤ 2 * (2 ^ N * e) := by
      intro π
      have hb := bad_sum n N m hn hN (Q.map π.symm.toEmbedding)
      simp_rw [bal_map]
      exact hb
    have h2 := Finset.sum_le_sum (fun π (_ : π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n)))) => this π)
    rw [Finset.sum_const, hcardperm, nsmul_eq_mul] at h2
    exact h2
  have hF : FF n m Q C0 ≤ (Nat.factorial n : ℝ) * (2 * e) := by
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    rw [hC] at hD
    nlinarith
  have hPc : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have key : (Nat.factorial n : ℝ) * ∑ C ∈ P, (if Balanced n m C Q then (0 : ℝ) else 1)
      ≤ (Nat.factorial n : ℝ) * ((P.card : ℝ) * (2 * e)) := by
    rw [← hA, hB]
    have := mul_le_mul_of_nonneg_left hF hPc
    linarith
  exact le_of_mul_le_mul_left key hfact

noncomputable def badC (n m : ℕ) {q : ℕ} (A : DetAlg (Fin n) q) (C : Finset (Fin n)) : ℝ :=
  (∑ j ∈ Finset.range q,
      (if Balanced n m C (A.queryAt (gCut n) j) then (0 : ℝ) else 1))
    + (if Balanced n m C (A.run (gCut n)) then (0 : ℝ) else 1)

lemma badC_nonneg (n m : ℕ) {q : ℕ} (A : DetAlg (Fin n) q) (C : Finset (Fin n)) :
    0 ≤ badC n m A C := by
  unfold badC
  have h1 : 0 ≤ ∑ j ∈ Finset.range q,
      (if Balanced n m C (A.queryAt (gCut n) j) then (0 : ℝ) else 1) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  have h2 : (0:ℝ) ≤ (if Balanced n m C (A.run (gCut n)) then (0 : ℝ) else 1) := by
    split_ifs <;> norm_num
  linarith

lemma u_bound' (n m N : ℕ) (hn : n = N + N) (hmn : 2 * m ≤ n)
    {q : ℕ} (A : DetAlg (Fin n) q) (C : Finset (Fin n)) (hC : C.card = N) :
    fC n m C (A.run (fC n m C))
      ≤ (n : ℝ) ^ 2 / 4 + ((n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2) * badC n m A C := by
  have hK : 0 ≤ (n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2 := by
    have hn' : (n : ℝ) = N + N := by exact_mod_cast hn
    have hmN : (m : ℝ) ≤ N := by
      have : m ≤ N := by omega
      exact_mod_cast this
    rw [hn']; nlinarith [sq_nonneg ((N : ℝ) - m), sq_nonneg (N : ℝ)]
  have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by positivity
  have hb0 := badC_nonneg n m A C
  by_cases hgood : (∀ j < q, Balanced n m C (A.queryAt (gCut n) j)) ∧ Balanced n m C (A.run (gCut n))
  · obtain ⟨hq, hS⟩ := hgood
    have hans : A.answers (fC n m C) q = A.answers (gCut n) q := by
      apply answers_eq
      intro j hj
      exact balanced_eq n m C _ (hq j hj)
    have hrun : A.run (fC n m C) = A.run (gCut n) := by
      unfold DetAlg.run; rw [hans]
    rw [hrun, balanced_eq n m C _ hS]
    have := gCut_le n (A.run (gCut n))
    nlinarith [mul_nonneg hK hb0]
  · have hbad : 1 ≤ badC n m A C := by
      unfold badC
      have h2 : (0:ℝ) ≤ (if Balanced n m C (A.run (gCut n)) then (0 : ℝ) else 1) := by
        split_ifs <;> norm_num
      have h1 : 0 ≤ ∑ j ∈ Finset.range q,
          (if Balanced n m C (A.queryAt (gCut n) j) then (0 : ℝ) else 1) :=
        Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
      by_cases hS : Balanced n m C (A.run (gCut n))
      · have : ∃ j < q, ¬ Balanced n m C (A.queryAt (gCut n) j) := by
          by_contra hcon
          push_neg at hcon
          exact hgood ⟨hcon, hS⟩
        obtain ⟨j, hj, hjb⟩ := this
        have hsingle : (if Balanced n m C (A.queryAt (gCut n) j) then (0 : ℝ) else 1)
            ≤ ∑ j ∈ Finset.range q,
              (if Balanced n m C (A.queryAt (gCut n) j) then (0 : ℝ) else 1) :=
          Finset.single_le_sum (f := fun j => (if Balanced n m C (A.queryAt (gCut n) j) then (0 : ℝ) else 1))
            (fun j _ => by split_ifs <;> norm_num) (Finset.mem_range.mpr hj)
        have hval : (if Balanced n m C (A.queryAt (gCut n) j) then (0 : ℝ) else 1) = 1 := if_neg hjb
        linarith
      · have hval : (if Balanced n m C (A.run (gCut n)) then (0 : ℝ) else 1) = 1 := if_neg hS
        linarith
    have := fC_le n m N hn hmn C hC (A.run (fC n m C))
    nlinarith [mul_le_mul_of_nonneg_left hbad hK]

lemma main (n m N : ℕ) (hn : n = N + N) (hmn : 2 * m ≤ n) (hN : 0 < N)
    (q : ℕ) (hq : (q : ℝ) < Real.exp (((m : ℝ) / n) ^ 2 * n / 8)) (A : DetAlg (Fin n) q) :
    ∑ C ∈ (Finset.univ : Finset (Fin n)).powersetCard N, fC n m C (A.run (fC n m C)) ≤
      (n.choose N : ℝ) *
        ((n : ℝ) ^ 2 / 4 + (2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 8)) +
          2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 4))) *
          ((n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2)) := by
  classical
  set P := (Finset.univ : Finset (Fin n)).powersetCard N with hP
  set K : ℝ := (n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2 with hKdef
  set β : ℝ := 2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 8)) +
            2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 4)) with hβ
  have hn' : (n : ℝ) = N + N := by exact_mod_cast hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 ≤ K := by
    have hmN : (m : ℝ) ≤ N := by
      have : m ≤ N := by omega
      exact_mod_cast this
    rw [hKdef, hn']; nlinarith [sq_nonneg ((N : ℝ) - m), sq_nonneg (N : ℝ)]
  set x : ℝ := ((m : ℝ) / n) ^ 2 * n with hx
  have hx0 : 0 ≤ x := by positivity
  have hxe : -((m : ℝ) ^ 2) / (2 * N) = -x := by
    rw [hx, hn']; field_simp; ring
  have hbeta : ((q : ℝ) + 1) * (2 * Real.exp (-x)) ≤ β := by
    rw [hβ]; exact numeric x hx0 q hq
  have hPc : (P.card : ℝ) = (n.choose N : ℝ) := by
    rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hPc0 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hcnt : ∀ Q : Finset (Fin n),
      ∑ C ∈ P, (if Balanced n m C Q then (0 : ℝ) else 1) ≤ (P.card : ℝ) * (2 * Real.exp (-x)) := by
    intro Q
    have := count_bad n N m hn hN Q
    rw [hxe] at this
    exact this
  have h1 : ∑ C ∈ P, fC n m C (A.run (fC n m C)) ≤ ∑ C ∈ P, ((n : ℝ) ^ 2 / 4 + K * badC n m A C) :=
    Finset.sum_le_sum (fun C hC => u_bound' n m N hn hmn A C (Finset.mem_powersetCard.mp hC).2)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ∑ C ∈ P, badC n m A C ≤ ((q : ℝ) + 1) * ((P.card : ℝ) * (2 * Real.exp (-x))) := by
    unfold badC
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have h3 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range q) => hcnt (A.queryAt (gCut n) j))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
    have h4 := hcnt (A.run (gCut n))
    linarith
  have h5 : ((q : ℝ) + 1) * ((P.card : ℝ) * (2 * Real.exp (-x))) ≤ (P.card : ℝ) * β := by
    have := mul_le_mul_of_nonneg_left hbeta hPc0
    linarith
  have h6 := mul_le_mul_of_nonneg_left (h2.trans h5) hK
  rw [← hPc]
  nlinarith

end Pdcc79144

open NonmonotoneSubmod.QueryLB in
theorem solution (n m q : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (hq : (q : ℝ) < Real.exp (((m : ℝ) / n) ^ 2 * n / 8)) (A : DetAlg (Fin n) q) :
    ∑ C ∈ Finset.univ.powersetCard (n / 2), fC n m C (A.run (fC n m C)) ≤
      (n.choose (n / 2) : ℝ) *
        ((n : ℝ) ^ 2 / 4 + (2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 8)) +
          2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 4))) *
          ((n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2)) := by
  obtain ⟨N, hN⟩ := hn
  have hN2 : n / 2 = N := by omega
  have hNpos : 0 < N := by omega
  rw [hN2]
  exact Pdcc79144.main n m N hN hmn hNpos q hq A
