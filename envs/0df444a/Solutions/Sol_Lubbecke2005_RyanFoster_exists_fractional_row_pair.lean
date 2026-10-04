-- Prove2me | solution 1 for Lubbecke2005.RyanFoster.exists_fractional_row_pair
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T14:04:21.496389+00:00
-- url     : https://prove2.me/submissions/471d645e-3bd2-445b-bfa7-8ceeedf5b36c

import Definitions.Def_BasicSolution
import Definitions.Def_Lubbecke2005_RyanFoster_SetPartitioning
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

open Matrix LinearOptimization Lubbecke2005.RyanFoster
open scoped BigOperators

set_option autoImplicit false

/- A direction annihilating the equality rows and vanishing at every zero
   coordinate of a basic solution must vanish. The selected active normals
   are n independent vectors in R^n, hence span the whole space. -/
private lemma basic_kernel_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hbasic : IsBasicSolution (stdFormSystem A b) x)
    (d : Fin n → ℝ) (hrow : ∀ r, A r ⬝ᵥ d = 0)
    (hzero : ∀ j, x j = 0 → d j = 0) : d = 0 := by
  classical
  obtain ⟨s, hs, hactive, hlin⟩ := hbasic.2
  have hspan := hlin.span_eq_top_of_card_eq_finrank' (by simpa using hs)
  let K : Submodule ℝ (Fin n → ℝ) :=
    { carrier := {v | v ⬝ᵥ d = 0}
      zero_mem' := by simp
      add_mem' := by intro u v hu hv; simp_all [add_dotProduct]
      smul_mem' := by intro a u hu; simp_all [smul_dotProduct] }
  have hle : Submodule.span ℝ
      (Set.range (fun i : s => (stdFormSystem A b i.1).a)) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    change (stdFormSystem A b i).a ⬝ᵥ d = 0
    cases i with
    | inl r => exact hrow r
    | inr j =>
      have hj : x j = 0 := by
        simpa [stdFormSystem, LinearConstraint.IsActiveAt, single_dotProduct] using
          hactive (Sum.inr j) hi
      simpa [stdFormSystem, single_dotProduct] using hzero j hj
  rw [hspan] at hle
  exact dotProduct_self_eq_zero.mp (hle (show d ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) from trivial))

private lemma basic_column_nonzero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hbasic : IsBasicSolution (stdFormSystem A b) x)
    (j : Fin n) (hj : x j ≠ 0) : ∃ r, A r j ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hd := basic_kernel_zero A b x hbasic (Pi.single j 1)
    (fun r => by simp [dotProduct_single, h r]) (by
      intro k hk
      have hkj : k ≠ j := by rintro rfl; exact hj hk
      simp [hkj])
  have he := congrFun hd j
  simp at he

private lemma basic_columns_distinct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hbasic : IsBasicSolution (stdFormSystem A b) x)
    (j k : Fin n) (hj : x j ≠ 0) (hk : x k ≠ 0) (hjk : j ≠ k) :
    ∃ r, A r j ≠ A r k := by
  classical
  by_contra h
  push Not at h
  have hd := basic_kernel_zero A b x hbasic (Pi.single j 1 - Pi.single k 1)
    (fun r => by simp [dotProduct_sub, dotProduct_single, h r]) (by
      intro l hl
      have hlj : l ≠ j := by rintro rfl; exact hj hl
      have hlk : l ≠ k := by rintro rfl; exact hk hl
      simp [hlj, hlk])
  have he := congrFun hd j
  simp [hjk] at he

/- Two positive columns cover r. If s includes the first and excludes the
   second, the pair sum is positive and strictly smaller than the row sum. -/
private lemma pair_between {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : IsZeroOneMatrix A) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hrows : ∀ r, ∑ j, A r j * x j = 1)
    (r s : Fin m) (j k : Fin n)
    (hrj : A r j = 1) (hrk : A r k = 1)
    (hsj : A s j = 1) (hsk : A s k = 0)
    (hj : 0 < x j) (hk : 0 < x k) :
    0 < pairCover A x r s ∧ pairCover A x r s < 1 := by
  have hnonneg : ∀ r j, 0 ≤ A r j := by
    intro r j; rcases hA r j with h | h <;> simp [h]
  constructor
  · apply Finset.sum_pos' (fun l _ => mul_nonneg (mul_nonneg (hnonneg r l)
      (hnonneg s l)) (hx l))
    exact ⟨j, Finset.mem_univ j, by simpa [hrj, hsj] using hj⟩
  · unfold pairCover
    rw [← hrows r]
    apply Finset.sum_lt_sum
    · intro l _
      rcases hA s l with h | h
      · simp [h, mul_nonneg (hnonneg r l) (hx l)]
      · simp [h]
    · exact ⟨k, Finset.mem_univ k, by simpa [hrk, hsk] using hk⟩

/-- Ryan–Foster's fractional row-pair lemma, Proposition 3 of
Lübbecke–Desrosiers (2005), using the argument of Barnhart et al., §5.1. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : IsZeroOneMatrix A) (lam : Fin n → ℝ)
    (hbasic : LinearOptimization.IsBasicFeasibleSolution
      (LinearOptimization.stdFormSystem A (fun _ => 1)) lam)
    (hfrac : ¬ IsZeroOneVector lam) :
    ∃ r s : Fin m, 0 < pairCover A lam r s ∧ pairCover A lam r s < 1 := by
  classical
  have hrows : ∀ r, ∑ j, A r j * lam j = 1 := by
    intro r
    exact hbasic.2 (Sum.inl r)
  have hlam : ∀ j, 0 ≤ lam j := by
    intro j
    simpa [stdFormSystem, LinearConstraint.IsSatisfiedAt, single_dotProduct] using
      hbasic.2 (Sum.inr j)
  have hnonneg : ∀ r j, 0 ≤ A r j := by
    intro r j; rcases hA r j with h | h <;> simp [h]
  obtain ⟨j, hj⟩ := not_forall.mp hfrac
  have hj0 : lam j ≠ 0 := fun h => hj (Or.inl h)
  have hj1 : lam j ≠ 1 := fun h => hj (Or.inr h)
  have hjpos : 0 < lam j := lt_of_le_of_ne (hlam j) (Ne.symm hj0)
  obtain ⟨r, hr⟩ := basic_column_nonzero A (fun _ => 1) lam hbasic.1 j hj0
  have hrj : A r j = 1 := (hA r j).resolve_left hr
  have hother : ∃ k, k ≠ j ∧ 0 < A r k * lam k := by
    by_contra h
    push Not at h
    have hsum : (∑ k, A r k * lam k) = A r j * lam j := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        exact le_antisymm (h k hkj) (mul_nonneg (hnonneg r k) (hlam k))
      · simp
    apply hj1
    simpa [hrj] using hsum.symm.trans (hrows r)
  obtain ⟨k, hkj, hkpos⟩ := hother
  have hrk : A r k = 1 := (hA r k).resolve_left (by
    intro h; simp [h] at hkpos)
  have hkpos' : 0 < lam k := by simpa [hrk] using hkpos
  obtain ⟨s, hs⟩ := basic_columns_distinct A (fun _ => 1) lam hbasic.1
    j k hj0 (ne_of_gt hkpos') (Ne.symm hkj)
  refine ⟨r, s, ?_⟩
  rcases hA s j with hsj | hsj <;> rcases hA s k with hsk | hsk
  · exact (hs (hsj.trans hsk.symm)).elim
  · exact pair_between A hA lam hlam hrows r s k j hrk hrj hsk hsj hkpos' hjpos
  · exact pair_between A hA lam hlam hrows r s j k hrj hrk hsj hsk hjpos hkpos'
  · exact (hs (hsj.trans hsk.symm)).elim
