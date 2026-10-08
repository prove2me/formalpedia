-- Prove2me | solution 1 for KellyReversibility.Genetics.ewens_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:08:22.862679+00:00
-- url     : https://prove2.me/submissions/92d79936-b214-4e8c-969b-d7204fcde787

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal
import Definitions.Def_KellyReversibility_Genetics_Ewens

set_option autoImplicit false

namespace EwensAux8eb

open Finset

noncomputable def F (ν : ℝ) (i c : ℕ) : ℝ := (ν / (i : ℝ)) ^ c / (c.factorial : ℝ)

noncomputable def P (ν : ℝ) (T : Finset ℕ) (s : Multiset ℕ) : ℝ := ∏ j ∈ T, F ν j (s.count j)

lemma P_eq_self (ν : ℝ) (T : Finset ℕ) (s : Multiset ℕ) (h : s.toFinset ⊆ T) :
    P ν T s = P ν s.toFinset s := by
  unfold P
  symm
  apply Finset.prod_subset h
  intro j _ hj
  have : s.count j = 0 := by
    rw [Multiset.count_eq_zero]; simpa using hj
  simp [F, this]

lemma P_congr (ν : ℝ) (T T' : Finset ℕ) (s : Multiset ℕ) (h : s.toFinset ⊆ T)
    (h' : s.toFinset ⊆ T') : P ν T s = P ν T' s := by
  rw [P_eq_self ν T s h, P_eq_self ν T' s h']

lemma F_step (ν : ℝ) (i c : ℕ) (hi : i ≠ 0) :
    ((c + 1 : ℕ) : ℝ) * (i : ℝ) * F ν i (c + 1) = ν * F ν i c := by
  unfold F
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi
  have key : ν / (i : ℝ) * (i : ℝ) = ν := div_mul_cancel₀ ν hi'
  generalize ν / (i : ℝ) = a at key ⊢
  subst key
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hf : (c.factorial : ℝ) ≠ 0 := by positivity
  have hc1 : (c : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma key_A (ν : ℝ) (T : Finset ℕ) (s : Multiset ℕ) (hpos : ∀ x ∈ s, 0 < x)
    (hT : s.toFinset ⊆ T) :
    (s.sum : ℝ) * P ν T s = ν * ∑ i ∈ s.toFinset, P ν T (s.erase i) := by
  rw [Finset.sum_multiset_count s]
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have his : i ∈ s := by simpa using hi
  have hiT : i ∈ T := hT hi
  have hi0 : i ≠ 0 := (hpos i his).ne'
  obtain ⟨c, hc⟩ : ∃ c, s.count i = c + 1 :=
    ⟨s.count i - 1, by have := Multiset.count_pos.mpr his; omega⟩
  unfold P
  rw [← Finset.mul_prod_erase T _ hiT, ← Finset.mul_prod_erase T _ hiT]
  have hrest : ∏ j ∈ T.erase i, F ν j ((s.erase i).count j) = ∏ j ∈ T.erase i, F ν j (s.count j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Multiset.count_erase_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, Multiset.count_erase_self, hc]
  simp only [nsmul_eq_mul, Nat.add_sub_cancel]
  rw [← mul_assoc, ← mul_assoc, ← F_step ν i c hi0]
  push_cast
  ring

noncomputable def Sm (m : ℕ) : Finset (Multiset ℕ) :=
  (Finset.univ : Finset (Nat.Partition m)).image Nat.Partition.parts

lemma mem_Sm (m : ℕ) (s : Multiset ℕ) : s ∈ Sm m ↔ (∀ x ∈ s, 0 < x) ∧ s.sum = m := by
  unfold Sm
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨fun x hx => p.parts_pos hx, p.parts_sum⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨s, fun hx => h1 _ hx, h2⟩, rfl⟩

lemma Sm_sub (m : ℕ) (s : Multiset ℕ) (hs : s ∈ Sm m) : s.toFinset ⊆ Finset.Icc 1 m := by
  rw [mem_Sm] at hs
  intro x hx
  have hxs : x ∈ s := by simpa using hx
  have h1 := hs.1 x hxs
  have h2 := Multiset.le_sum_of_mem hxs
  rw [Finset.mem_Icc]
  omega

noncomputable def g (ν : ℝ) (m : ℕ) : ℝ := ∑ s ∈ Sm m, P ν (Finset.Icc 1 m) s

lemma key_B (ν : ℝ) (T : Finset ℕ) (n : ℕ) :
    ∑ s ∈ Sm n, ∑ i ∈ s.toFinset, P ν T (s.erase i) =
      ∑ i ∈ Finset.Icc 1 n, ∑ t ∈ Sm (n - i), P ν T t := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1.erase x.2⟩) (fun y _ => ⟨y.1 ::ₘ y.2, y.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨s, i⟩ h
    simp only [Finset.mem_sigma] at h ⊢
    obtain ⟨hs, hi⟩ := h
    have his : i ∈ s := by simpa using hi
    rw [mem_Sm] at hs
    have h1 := hs.1 i his
    have h2 := Multiset.le_sum_of_mem his
    have h3 := Multiset.sum_erase his
    refine ⟨by rw [Finset.mem_Icc]; omega, ?_⟩
    rw [mem_Sm]
    refine ⟨fun x hx => hs.1 x (Multiset.mem_of_mem_erase hx), ?_⟩
    omega
  · rintro ⟨i, t⟩ h
    simp only [Finset.mem_sigma] at h ⊢
    obtain ⟨hi, ht⟩ := h
    rw [Finset.mem_Icc] at hi
    rw [mem_Sm] at ht
    refine ⟨?_, by simp⟩
    rw [mem_Sm]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Multiset.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact ht.1 x hx
    · rw [Multiset.sum_cons]; omega
  · rintro ⟨s, i⟩ h
    simp only [Finset.mem_sigma] at h
    have his : i ∈ s := by simpa using h.2
    simp [Multiset.cons_erase his]
  · rintro ⟨i, t⟩ _
    simp
  · rintro ⟨s, i⟩ _
    rfl

lemma g_zero (ν : ℝ) : g ν 0 = 1 := by
  have : Sm 0 = {0} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨by rw [mem_Sm]; simp, ?_⟩
    intro s hs
    rw [mem_Sm] at hs
    rw [Multiset.sum_eq_zero_iff] at hs
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have := hs.1 x hx
    have := hs.2 x hx
    omega
  unfold g
  rw [this]
  simp [P]

lemma g_rec (ν : ℝ) (n : ℕ) :
    (n : ℝ) * g ν n = ν * ∑ j ∈ Finset.range n, g ν j := by
  unfold g
  rw [Finset.mul_sum]
  have h1 : ∀ s ∈ Sm n, (n : ℝ) * P ν (Finset.Icc 1 n) s
      = ν * ∑ i ∈ s.toFinset, P ν (Finset.Icc 1 n) (s.erase i) := by
    intro s hs
    have hs' := (mem_Sm n s).1 hs
    rw [← key_A ν _ s hs'.1 (Sm_sub n s hs), hs'.2]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, key_B]
  congr 1
  have h2 : ∀ i ∈ Finset.Icc 1 n, ∑ t ∈ Sm (n - i), P ν (Finset.Icc 1 n) t
      = ∑ t ∈ Sm (n - i), P ν (Finset.Icc 1 (n - i)) t := by
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    apply P_congr
    · intro x hx
      have := Sm_sub _ t ht hx
      rw [Finset.mem_Icc] at this ⊢
      omega
    · exact Sm_sub _ t ht
  rw [Finset.sum_congr rfl h2]
  have h3 : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := rfl
  rw [h3, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  rw [← Finset.sum_range_reflect (fun j => ∑ s ∈ Sm j, P ν (Finset.Icc 1 j) s) n]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have : n - (1 + k) = n - 1 - k := by omega
  rw [this]

noncomputable def r (ν : ℝ) (n : ℕ) : ℝ := (∏ k ∈ Finset.range n, (ν + k)) / (n.factorial : ℝ)

lemma r_succ (ν : ℝ) (n : ℕ) : r ν (n + 1) * ((n : ℝ) + 1) = r ν n * (ν + n) := by
  unfold r
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma r_sum (ν : ℝ) (hν : 0 < ν) (n : ℕ) :
    ν * ∑ j ∈ Finset.range n, r ν j = (n : ℝ) * r ν n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have := r_succ ν n
    push_cast
    linarith

lemma g_eq_r (ν : ℝ) (hν : 0 < ν) (n : ℕ) : g ν n = r ν n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [g_zero]; simp [r]
    · have h1 := g_rec ν n
      have h2 := r_sum ν hν n
      rw [Finset.sum_congr rfl (fun j hj => ih j (Finset.mem_range.1 hj)), h2] at h1
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      exact mul_left_cancel₀ hn' h1

lemma fallingP_eq (x : ℝ) (n : ℕ) :
    AppliedComb.GenFun.fallingP x n = ∏ k ∈ Finset.range n, (x - k) := by
  induction n generalizing x with
  | zero => simp [AppliedComb.GenFun.fallingP]
  | succ n ih =>
    rw [AppliedComb.GenFun.fallingP, ih, Finset.prod_range_succ']
    push_cast
    rw [mul_comm]
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      ring
    · ring

lemma binom_eq_r (ν : ℝ) (n : ℕ) :
    AppliedComb.GenFun.binomReal (ν + (n : ℝ) - 1) n = r ν n := by
  unfold AppliedComb.GenFun.binomReal r
  rw [fallingP_eq]
  congr 1
  rw [← Finset.prod_range_reflect (fun k : ℕ => ν + (k : ℝ)) n]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

lemma r_pos (ν : ℝ) (hν : 0 < ν) (n : ℕ) : 0 < r ν n := by
  unfold r
  apply div_pos
  · apply Finset.prod_pos
    intro k _
    positivity
  · positivity

end EwensAux8eb

open KellyReversibility.Genetics in
theorem solution (ν : ℝ) (hν : 0 < ν) (n : ℕ) (hn : 2 ≤ n) :
    (∀ p : Nat.Partition n, 0 < ewens ν n p) ∧ ∑ p : Nat.Partition n, ewens ν n p = 1 := by
  have hC : AppliedComb.GenFun.binomReal (ν + (n : ℝ) - 1) n = EwensAux8eb.r ν n :=
    EwensAux8eb.binom_eq_r ν n
  have hrpos := EwensAux8eb.r_pos ν hν n
  have hE : ∀ p : Nat.Partition n, ewens ν n p
      = (EwensAux8eb.r ν n)⁻¹ * EwensAux8eb.P ν (Finset.Icc 1 n) p.parts := by
    intro p
    unfold ewens
    rw [hC]
    rfl
  refine ⟨?_, ?_⟩
  · intro p
    rw [hE]
    apply mul_pos (inv_pos.mpr hrpos)
    unfold EwensAux8eb.P
    apply Finset.prod_pos
    intro i hi
    rw [Finset.mem_Icc] at hi
    unfold EwensAux8eb.F
    have : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
    positivity
  · simp_rw [hE]
    rw [← Finset.mul_sum]
    have hg : ∑ p : Nat.Partition n, EwensAux8eb.P ν (Finset.Icc 1 n) p.parts
        = EwensAux8eb.g ν n := by
      unfold EwensAux8eb.g EwensAux8eb.Sm
      rw [Finset.sum_image]
      intro a _ b _ h
      exact Nat.Partition.ext h
    rw [hg, EwensAux8eb.g_eq_r ν hν n]
    exact inv_mul_cancel₀ hrpos.ne'
