-- Prove2me | solution 1 for MakespanSparse.Thin.thin_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:49:32.989777+00:00
-- url     : https://prove2.me/submissions/7bea4763-b962-4826-be2f-b220a9e79fc7

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP
import Theorems.Thm_MakespanSparse_Thin_exists_disjoint_equal_column_sums
import Theorems.Thm_MakespanSparse_Thin_potential_min_complex_le_one
import Theorems.Thm_MakespanSparse_Thin_potential_min_complex_support_le

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

/-- The exchange step of Lemma 3 (Eisenbrand–Shmonin), restricted to a set `A ∪ B` of
configurations: for disjoint nonempty `A, B ⊆ supp(x)` with `Mx^A = Mx^B`, the solution
`x - λx^A + λx^B`, `λ = min_{c ∈ A} x_c`, has strictly smaller support. -/
lemma MSThin_exchange_support {d : ℕ} {π : Fin d → ℕ} {T : ℕ} {b : Fin d → ℕ} {m : ℕ}
    (x : (Fin d → ℕ) →₀ ℕ) (hx : IsConfIPSolution π T b m x)
    (A B : Finset (Fin d → ℕ)) (hA : A ⊆ x.support) (hB : B ⊆ x.support) (hAB : Disjoint A B)
    (hAne : A.Nonempty) (hsum : ∑ c ∈ A, c = ∑ c ∈ B, c) (hcard : A.card = B.card) :
    ∃ l : ℕ, (∀ c ∈ A, l ≤ x c) ∧ IsConfIPSolution π T b m ((x - ind A l) + ind B l) ∧
      ((x - ind A l) + ind B l).support.card < x.support.card := by
  classical
  obtain ⟨cs, hcsA, hcsmin⟩ := Finset.exists_mem_eq_inf' hAne (fun c => x c)
  set l := A.inf' hAne (fun c => x c) with hl
  have hlle : ∀ c ∈ A, l ≤ x c := fun c hc => Finset.inf'_le _ hc
  have hxA := decomp x A l hlle
  have hBconf : ∀ c ∈ (ind B l).support, IsConfig π T c :=
    fun c hc => hx.1 c (hB (ind_support B l hc))
  have hsol : IsConfIPSolution π T b m ((x - ind A l) + ind B l) :=
    exch (hxA ▸ hx) hBconf (by rw [S_ind, S_ind, hsum]) (by rw [N_ind, N_ind, hcard])
  refine ⟨l, hlle, hsol, Finset.card_lt_card ?_⟩
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨cs, hA hcsA, ?_⟩
    rw [Finsupp.mem_support_iff, not_not, Finsupp.add_apply, sub_ind_apply, ind_apply,
      if_pos hcsA, if_neg (Finset.disjoint_left.1 hAB hcsA), ← hcsmin]
    simp
  · intro c hc
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, sub_ind_apply, ind_apply] at hc
    by_cases hcB : c ∈ B
    · exact hB hcB
    · rw [if_neg hcB] at hc
      rw [Finsupp.mem_support_iff]; omega

theorem solution (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k) (T : ℕ) (hT : 0 < T)
    (b : Fin d → ℕ) (m : ℕ)
    (hfeas : ∃ x, IsConfIPSolution π T b m x) :
    ∃ x, IsConfIPSolution π T b m x ∧
      (∀ c, 1 < x c → IsSimple T c) ∧
      (x.support.card : ℝ) ≤ 4 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T) ∧
      ((∑ c ∈ x.support.filter (fun c => ¬ IsSimple T c), x c : ℕ) : ℝ) ≤
        2 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T) := by
  classical
  set L : ℝ := 2 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T) with hL
  -- a solution of minimum potential Φ ...
  have hP : ∃ n, ∃ x, IsConfIPSolution π T b m x ∧ potential T x = n := by
    obtain ⟨x, hx⟩ := hfeas; exact ⟨_, x, hx, rfl⟩
  set n0 := Nat.find hP with hn0
  have hQ : ∃ k, ∃ x, IsConfIPSolution π T b m x ∧ potential T x = n0 ∧ x.support.card = k := by
    obtain ⟨x, hx, hpx⟩ := Nat.find_spec hP; exact ⟨_, x, hx, hpx, rfl⟩
  -- ... and, among those, of minimum support
  obtain ⟨x, hx, hpx, hcx⟩ := Nat.find_spec hQ
  have hmin : ∀ y, IsConfIPSolution π T b m y → potential T x ≤ potential T y := by
    intro y hy; rw [hpx]; exact Nat.find_min' hP ⟨y, hy, rfl⟩
  have hminsupp : ∀ y, IsConfIPSolution π T b m y → potential T y = n0 →
      x.support.card ≤ y.support.card := by
    intro y hy hpy; rw [hcx]; exact Nat.find_min' hQ ⟨y, hy, hpy, rfl⟩
  -- P1 and P2
  have hP1 := potential_min_complex_le_one d π hπ T hT b m x hx hmin
  have hP2 := potential_min_complex_support_le d π hπ T hT b m x hx hmin
  -- the simple part of the support is small (Lemma 3 restricted to simple configurations)
  have hsimple : ((x.support.filter (fun c => IsSimple T c)).card : ℝ) ≤ L := by
    by_contra hgt
    push Not at hgt
    set xs := x.filter (fun c => IsSimple T c) with hxs
    have hxss : xs.support = x.support.filter (fun c => IsSimple T c) := by
      rw [hxs, Finsupp.support_filter]
    have hxssub : ∀ c ∈ xs.support, c ∈ x.support ∧ IsSimple T c := by
      intro c hc; rw [hxss, Finset.mem_filter] at hc; exact hc
    obtain ⟨A, B, hA, hB, hAB, hAne, -, hsum, hcard⟩ :=
      exists_disjoint_equal_column_sums d π hπ T hT xs
        (fun c hc => hx.1 c (hxssub c hc).1) (by rw [hxss]; exact hgt)
    obtain ⟨l, hlle, hsol, hlt⟩ := MSThin_exchange_support x hx A B
      (fun c hc => (hxssub c (hA hc)).1) (fun c hc => (hxssub c (hB hc)).1) hAB hAne hsum hcard
    have hpot : potential T ((x - ind A l) + ind B l) = n0 := by
      have e := pot_add T (x - ind A l) (ind A l)
      rw [← decomp x A l hlle] at e
      rw [pot_add, ← hpx, e, pot_ind, pot_ind,
        Finset.sum_eq_zero (fun c hc => if_pos (hxssub c (hA hc)).2),
        Finset.sum_eq_zero (fun c hc => if_pos (hxssub c (hB hc)).2)]
    have := hminsupp _ hsol hpot
    omega
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · intro c hc
    by_contra hcs
    have := hP1 c hcs
    omega
  · have hsplit := Finset.card_filter_add_card_filter_not
      (s := x.support) (fun c => IsSimple T c)
    have : (x.support.card : ℝ) = ((x.support.filter (fun c => IsSimple T c)).card : ℝ) +
        ((x.support.filter (fun c => ¬ IsSimple T c)).card : ℝ) := by
      rw [← hsplit]; push_cast; ring
    rw [this]
    have e4 : 4 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T) = L + L := by
      rw [hL]; ring
    rw [e4]
    exact add_le_add hsimple hP2
  · refine le_trans ?_ hP2
    have : ∑ c ∈ x.support.filter (fun c => ¬ IsSimple T c), x c ≤
        ∑ c ∈ x.support.filter (fun c => ¬ IsSimple T c), 1 :=
      Finset.sum_le_sum fun c hc => hP1 c (Finset.mem_filter.1 hc).2
    rw [Finset.sum_const, smul_eq_mul, mul_one] at this
    exact_mod_cast this
