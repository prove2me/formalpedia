-- Prove2me | solution 1 for MomentSearch.Supplement.sparse_sketch_hard_fibre
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:58:06.646355+00:00
-- url     : https://prove2.me/submissions/d2cbe439-baee-4f9e-8713-d9f33a5b1274

import Mathlib
import Definitions.Def_MomentSearch_OPT
import Theorems.Thm_MomentSearch_kraft_average_depth

open Finset MomentSearch

private noncomputable def empirical {n q : ℕ} (u : Fin q → Fin n) (j : Fin n) : ℝ :=
  (∑ i, if u i = j then (1 : ℝ) else 0) / q

private theorem empirical_eval {n q : ℕ} (u : Fin q → Fin n) (f : Fin n → ℝ) :
    ∑ j, empirical u j * f j = (∑ i, f (u i)) / q := by
  classical
  simp only [empirical, div_mul_eq_mul_div, ← sum_div, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp

private theorem empirical_mem {n q : ℕ} (hq : 0 < q) (u : Fin q → Fin n) :
    empirical u ∈ stdSimplex ℝ (Fin n) := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold empirical
    positivity
  · simpa [Nat.ne_of_gt hq] using empirical_eval u (fun _ => 1)

private theorem empirical_sparse {n q : ℕ} (u : Fin q → Fin n) :
    (Function.support (empirical u)).ncard ≤ q := by
  classical
  have sub : Function.support (empirical u) ⊆ Set.range u := by
    intro j hj
    by_contra h
    have hh : ∀ i, u i ≠ j := fun i e => h ⟨i,e⟩
    exact hj (by simp [empirical,hh])
  apply (Set.ncard_le_ncard sub).trans
  simpa using (Set.ncard_image_le (f := u) (Set.finite_univ : (Set.univ : Set (Fin q)).Finite))

private theorem kraft_four {n : ℕ} (hn : 2 ≤ n) (T : Strategy n) :
    ∑ j : Fin n, Real.exp (-((queries T j : ℝ) * Real.log 4)) ≤ 1 := by
  cases n with
  | zero => omega
  | succ m =>
    have K := (kraft_average_depth hn T m id Function.injective_id).1
    apply le_trans (sum_le_sum fun j _ => ?_) K
    rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num)]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

theorem solution {n q k : ℕ} (hn : 2 ≤ n) (hq : 0 < q)
    (X : Type) (σ : (Fin n → ℝ) → X)
    (hk : (k : ℝ) ≤ (q : ℝ) / 2 * Real.logb 2 n)
    (hfin : (σ '' stdSimplex ℝ (Fin n)).Finite)
    (hcard : (σ '' stdSimplex ℝ (Fin n)).ncard ≤ 2^k) :
    ∃ x ∈ σ '' stdSimplex ℝ (Fin n), ∀ T : MomentSearch.Strategy n,
      ∃ p ∈ stdSimplex ℝ (Fin n), σ p = x ∧
        (Function.support p).ncard ≤ q ∧ Real.logb 2 n / 4 ≤ MomentSearch.cost p T := by
  classical
  let A := σ '' stdSimplex ℝ (Fin n)
  let : Fintype A := hfin.fintype
  let g (u : Fin q → Fin n) : A := ⟨σ (empirical u), _, empirical_mem hq u, rfl⟩
  let : Nonempty A := ⟨g (fun _ => ⟨0,by omega⟩)⟩
  let L := (q : ℝ) * Real.log n / 2
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have budget : (k : ℝ) * Real.log 2 ≤ L := by
    rw [Real.logb] at hk
    dsimp [L]
    calc
      _ ≤ ((q : ℝ) / 2 * (Real.log n / Real.log 2)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hk l2.le
      _ = _ := by field_simp
  have count : Fintype.card A ≤ 2^k := by
    simpa [A,Set.ncard,Nat.card_eq_fintype_card] using hcard
  have hb : Fintype.card A • Real.exp L ≤ ∑ _ : Fin q → Fin n, (1 : ℝ) := by
    simp only [nsmul_eq_mul,sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,
      Nat.cast_pow,mul_one]
    calc
      _ ≤ ((2:ℝ)^k) * Real.exp L := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact_mod_cast count
      _ = Real.exp ((k:ℝ)*Real.log 2 + L) := by
        rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ ≤ Real.exp ((q : ℝ)*Real.log n) := Real.exp_le_exp.mpr (by dsimp [L] at *; linarith)
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log hn']
  obtain ⟨x,hx⟩ := Fintype.exists_le_sum_fiber_of_nsmul_le_sum g hb
  let S := univ.filter (fun u => g u = x)
  have size : Real.exp L ≤ (S.card : ℝ) := by simpa [S] using hx
  have sne : S.Nonempty := card_pos.mp (by exact_mod_cast (Real.exp_pos L).trans_le size)
  refine ⟨x.val,x.property,fun T => ?_⟩
  let w (j : Fin n) := Real.exp (-((queries T j : ℝ) * Real.log 4))
  let W (u : Fin q → Fin n) := ∏ i, w (u i)
  have total : ∑ u, W u ≤ 1 := by
    have e := sum_pow' (univ : Finset (Fin n)) w q
    simp only [Fintype.piFinset_univ] at e
    exact e.ge.trans (pow_le_one₀ (sum_nonneg fun _ _ => (Real.exp_pos _).le) (kraft_four hn T))

  have restricted : ∑ u ∈ S, W u ≤ 1 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ S)
      (fun u _ _ => prod_nonneg fun i _ => (Real.exp_pos _).le)).trans total
  have ones : 1 ≤ ∑ _ ∈ S, Real.exp (-L) := by
    simp only [sum_const,nsmul_eq_mul,Real.exp_neg]
    rw [← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _),one_mul]
    exact size
  obtain ⟨u,hu,hweight⟩ := exists_le_of_sum_le sne (restricted.trans ones)
  refine ⟨empirical u, empirical_mem hq u, congrArg Subtype.val (mem_filter.mp hu).2,
    empirical_sparse u, ?_⟩
  have prod_eq : W u = Real.exp (-((∑ i, (queries T (u i) : ℝ)) * Real.log 4)) := by
    rw [sum_mul,← sum_neg_distrib,Real.exp_sum]
  rw [prod_eq,Real.exp_le_exp] at hweight
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [l4] at hweight
  rw [cost,empirical_eval,Real.logb,le_div_iff₀ hq']
  rw [div_div,div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  dsimp [L] at hweight
  linarith only [hweight]
