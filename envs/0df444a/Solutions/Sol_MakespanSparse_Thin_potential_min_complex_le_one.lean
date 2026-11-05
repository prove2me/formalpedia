-- Prove2me | solution 1 for MakespanSparse.Thin.potential_min_complex_le_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:45:13.83912+00:00
-- url     : https://prove2.me/submissions/7759b023-4221-4166-b345-e98a2bc339c2

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP
import Theorems.Thm_MakespanSparse_Thin_sparsification_lemma

open MakespanSparse.Thin

namespace MSThinAux

/-- `∑_c x_c c`, the left-hand side of the first equality system of [conf-IP]. -/
def S {d : ℕ} (x : (Fin d → ℕ) →₀ ℕ) : Fin d → ℕ := x.sum (fun c n => n • c)
/-- `∑_c x_c`, the left-hand side of the last equality of [conf-IP]. -/
def N {d : ℕ} (x : (Fin d → ℕ) →₀ ℕ) : ℕ := x.sum (fun _ n => n)

lemma S_add {d : ℕ} (x y : (Fin d → ℕ) →₀ ℕ) : S (x + y) = S x + S y :=
  Finsupp.sum_add_index' (by simp) (by intros; simp [add_smul])

lemma N_add {d : ℕ} (x y : (Fin d → ℕ) →₀ ℕ) : N (x + y) = N x + N y :=
  Finsupp.sum_add_index' (by simp) (by intros; rfl)

lemma pot_eq {d : ℕ} (T : ℕ) (x : (Fin d → ℕ) →₀ ℕ) :
    potential T x = x.sum (fun c n => if IsSimple T c then 0 else n * (supp c).card) := by
  unfold potential Finsupp.sum
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : IsSimple T c <;> simp [h]

lemma pot_add {d : ℕ} (T : ℕ) (x y : (Fin d → ℕ) →₀ ℕ) :
    potential T (x + y) = potential T x + potential T y := by
  simp only [pot_eq]
  exact Finsupp.sum_add_index' (by intros; split_ifs <;> simp) (by intros; split_ifs <;> ring)

lemma pot_single {d : ℕ} (T : ℕ) (c : Fin d → ℕ) (n : ℕ) :
    potential T (Finsupp.single c n) = if IsSimple T c then 0 else n * (supp c).card := by
  rw [pot_eq, Finsupp.sum_single_index]
  split_ifs <;> simp

lemma exch {d : ℕ} {π : Fin d → ℕ} {T : ℕ} {b : Fin d → ℕ} {m : ℕ}
    {y u v : (Fin d → ℕ) →₀ ℕ} (h : IsConfIPSolution π T b m (y + u))
    (hv : ∀ c ∈ v.support, IsConfig π T c) (hS : S v = S u) (hN : N v = N u) :
    IsConfIPSolution π T b m (y + v) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 (Finsupp.support_add hc) with hc | hc
    · apply h1
      rw [Finsupp.mem_support_iff] at hc ⊢
      rw [Finsupp.add_apply]; omega
    · exact hv c hc
  · change S (y + v) = b
    rw [S_add, hS, ← S_add]; exact h2
  · change N (y + v) = m
    rw [N_add, hN, ← N_add]; exact h3

/-- `λ x^A`: the vector with value `λ` on `A` and `0` elsewhere. -/
noncomputable def ind {d : ℕ} (A : Finset (Fin d → ℕ)) (l : ℕ) : (Fin d → ℕ) →₀ ℕ :=
  ∑ c ∈ A, Finsupp.single c l

lemma ind_apply {d : ℕ} (A : Finset (Fin d → ℕ)) (l : ℕ) (c : Fin d → ℕ) :
    ind A l c = if c ∈ A then l else 0 := by
  classical
  unfold ind
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

lemma ind_support {d : ℕ} (A : Finset (Fin d → ℕ)) (l : ℕ) : (ind A l).support ⊆ A := by
  intro c hc
  rw [Finsupp.mem_support_iff, ind_apply] at hc
  by_contra h; exact hc (if_neg h)

lemma ind_insert {d : ℕ} (A : Finset (Fin d → ℕ)) (a : Fin d → ℕ) (ha : a ∉ A) (l : ℕ) :
    ind (insert a A) l = Finsupp.single a l + ind A l := by
  classical
  unfold ind; rw [Finset.sum_insert ha]

lemma S_ind {d : ℕ} (A : Finset (Fin d → ℕ)) (l : ℕ) : S (ind A l) = l • ∑ c ∈ A, c := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [ind, S]
  | insert a s ha ih =>
    rw [ind_insert s a ha, S_add, ih, Finset.sum_insert ha, smul_add]
    simp [S, Finsupp.sum_single_index]

lemma N_ind {d : ℕ} (A : Finset (Fin d → ℕ)) (l : ℕ) : N (ind A l) = l * A.card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [ind, N]
  | insert a s ha ih =>
    rw [ind_insert s a ha, N_add, ih, Finset.card_insert_of_notMem ha]
    simp [N, Finsupp.sum_single_index]; ring

lemma pot_ind {d : ℕ} (T : ℕ) (A : Finset (Fin d → ℕ)) (l : ℕ) :
    potential T (ind A l) = ∑ c ∈ A, (if IsSimple T c then 0 else l * (supp c).card) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [ind, pot_eq]
  | insert a s ha ih =>
    rw [ind_insert s a ha, pot_add, pot_single, ih, Finset.sum_insert ha]

lemma decomp {d : ℕ} (x : (Fin d → ℕ) →₀ ℕ) (A : Finset (Fin d → ℕ)) (l : ℕ)
    (h : ∀ c ∈ A, l ≤ x c) : x = (x - ind A l) + ind A l := by
  refine (tsub_add_cancel_of_le ?_).symm
  intro c
  rw [ind_apply]
  split_ifs with hc
  · exact h c hc
  · exact Nat.zero_le _

lemma sub_ind_apply {d : ℕ} (x : (Fin d → ℕ) →₀ ℕ) (A : Finset (Fin d → ℕ)) (l : ℕ)
    (c : Fin d → ℕ) : (x - ind A l) c = x c - (if c ∈ A then l else 0) := by
  rw [Finsupp.tsub_apply, ind_apply]

end MSThinAux

open MSThinAux

theorem solution (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k)
    (T : ℕ) (hT : 0 < T) (b : Fin d → ℕ) (m : ℕ)
    (x : (Fin d → ℕ) →₀ ℕ) (hx : IsConfIPSolution π T b m x)
    (hmin : ∀ y, IsConfIPSolution π T b m y → potential T x ≤ potential T y) :
    ∀ c, ¬ IsSimple T c → x c ≤ 1 := by
  classical
  intro c hcx
  by_contra hlt
  push Not at hlt
  have hcs : c ∈ x.support := by rw [Finsupp.mem_support_iff]; omega
  have hcc : IsConfig π T c := hx.1 c hcs
  obtain ⟨c₁, c₂, hc₁, hc₂, -, -, h2c, hs₁, hs₂⟩ := sparsification_lemma d π hπ T c hcc hcx
  set u : (Fin d → ℕ) →₀ ℕ := Finsupp.single c 2 with hu
  set v : (Fin d → ℕ) →₀ ℕ := Finsupp.single c₁ 1 + Finsupp.single c₂ 1 with hv
  set y := x - u with hy
  have hxu : x = y + u := by
    refine (tsub_add_cancel_of_le ?_).symm
    intro e
    rw [hu, Finsupp.single_apply]
    split_ifs with he
    · subst he; omega
    · exact Nat.zero_le _
  have hsol : IsConfIPSolution π T b m (y + v) := by
    refine exch (u := u) (hxu ▸ hx) ?_ ?_ ?_
    · intro e he
      rcases Finset.mem_union.1 (Finsupp.support_add he) with he | he
      · have he := Finset.mem_singleton.1 (Finsupp.support_single_subset he)
        rw [he]; exact hc₁
      · have he := Finset.mem_singleton.1 (Finsupp.support_single_subset he)
        rw [he]; exact hc₂
    · rw [hv, hu, S_add]
      simp only [S, Finsupp.sum_single_index, zero_smul, one_smul]
      exact h2c.symm
    · rw [hv, hu, N_add]
      simp [N, Finsupp.sum_single_index]
  have hle := hmin _ hsol
  rw [hxu, pot_add, pot_add] at hle
  have hpu : potential T u = 2 * (supp c).card := by
    rw [hu, pot_single, if_neg hcx]
  have hpv : potential T v < 2 * (supp c).card := by
    rw [hv, pot_add, pot_single, pot_single]
    have h1 := Finset.card_lt_card hs₁
    have h2 := Finset.card_lt_card hs₂
    split_ifs <;> omega
  omega
