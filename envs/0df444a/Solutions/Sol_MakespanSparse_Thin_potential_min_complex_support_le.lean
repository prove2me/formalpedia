-- Prove2me | solution 1 for MakespanSparse.Thin.potential_min_complex_support_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:47:10.123203+00:00
-- url     : https://prove2.me/submissions/6ace97e6-9fc9-4e78-ac29-a21708305ed9

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP
import Theorems.Thm_MakespanSparse_Thin_exists_disjoint_equal_column_sums
import Theorems.Thm_MakespanSparse_Thin_potential_min_complex_le_one

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
    ((x.support.filter (fun c => ¬ IsSimple T c)).card : ℝ) ≤
      2 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T) := by
  classical
  by_contra hgt
  push Not at hgt
  set xt := x.filter (fun c => ¬ IsSimple T c) with hxt
  have hxts : xt.support = x.support.filter (fun c => ¬ IsSimple T c) := by
    rw [hxt, Finsupp.support_filter]
  have hxtsub : ∀ c ∈ xt.support, c ∈ x.support ∧ ¬ IsSimple T c := by
    intro c hc; rw [hxts, Finset.mem_filter] at hc; exact hc
  obtain ⟨A, B, hA, hB, hAB, hAne, hBne, hsum, hcard⟩ :=
    exists_disjoint_equal_column_sums d π hπ T hT xt
      (fun c hc => hx.1 c (hxtsub c hc).1) (by rw [hxts]; exact hgt)
  have hA1 : ∀ c ∈ A, 1 ≤ x c := fun c hc => by
    have := (hxtsub c (hA hc)).1; rw [Finsupp.mem_support_iff] at this; omega
  have hB1 : ∀ c ∈ B, 1 ≤ x c := fun c hc => by
    have := (hxtsub c (hB hc)).1; rw [Finsupp.mem_support_iff] at this; omega
  have hxA := decomp x A 1 hA1
  have hxB := decomp x B 1 hB1
  have hBconf : ∀ c ∈ (ind B 1).support, IsConfig π T c :=
    fun c hc => hx.1 c (hxtsub c (hB (ind_support B 1 hc))).1
  have hAconf : ∀ c ∈ (ind A 1).support, IsConfig π T c :=
    fun c hc => hx.1 c (hxtsub c (hA (ind_support A 1 hc))).1
  -- x' = x - x^A + x^B and x'' = x - x^B + x^A
  have hsol' : IsConfIPSolution π T b m ((x - ind A 1) + ind B 1) :=
    exch (hxA ▸ hx) hBconf (by rw [S_ind, S_ind, hsum]) (by rw [N_ind, N_ind, hcard])
  have hsol'' : IsConfIPSolution π T b m ((x - ind B 1) + ind A 1) :=
    exch (hxB ▸ hx) hAconf (by rw [S_ind, S_ind, hsum]) (by rw [N_ind, N_ind, hcard])
  have h1 := hmin _ hsol'
  have h2 := hmin _ hsol''
  have ePA := pot_add T (x - ind A 1) (ind A 1)
  have ePB := pot_add T (x - ind B 1) (ind B 1)
  rw [← hxA] at ePA
  rw [← hxB] at ePB
  rw [pot_add] at h1 h2
  -- hence Φ(x') = Φ(x), so x' is also a minimizer
  have hmin' : ∀ y, IsConfIPSolution π T b m y →
      potential T ((x - ind A 1) + ind B 1) ≤ potential T y := by
    intro y hy
    have := hmin y hy
    rw [pot_add]; omega
  obtain ⟨c, hcB⟩ := hBne
  have hcx : ¬ IsSimple T c := (hxtsub c (hB hcB)).2
  have hle := potential_min_complex_le_one d π hπ T hT b m _ hsol' hmin' c hcx
  have hcA : c ∉ A := Finset.disjoint_right.1 hAB hcB
  rw [Finsupp.add_apply, sub_ind_apply, ind_apply, if_neg hcA, if_pos hcB] at hle
  have := hB1 c hcB
  omega
