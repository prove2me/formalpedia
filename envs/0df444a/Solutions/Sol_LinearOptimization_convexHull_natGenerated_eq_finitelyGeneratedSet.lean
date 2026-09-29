-- Prove2me | solution 1 for LinearOptimization.convexHull_natGenerated_eq_finitelyGeneratedSet
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T03:12:22.865641+00:00
-- url     : https://prove2.me/submissions/432d3284-49c1-47e5-83d2-da3a96208dbc

import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_LinearOptimization_FinitelyGeneratedSet
import Theorems.Thm_LinearOptimization_finitely_generated_is_polyhedron

open LinearOptimization
open Matrix

private lemma polyhedron_convex {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron A b) := by
  intro u hu v hv a c ha hc hac i
  change b i ≤ A i ⬝ᵥ (a • u + c • v)
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hu i) ha
  have h2 := mul_le_mul_of_nonneg_left (hv i) hc
  calc
    b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
    _ ≤ a * (A i ⬝ᵥ u) + c * (A i ⬝ᵥ v) := add_le_add h1 h2

private def natGeneratedSet {n k r : ℕ} (x : Fin k → (Fin n → ℝ))
    (w : Fin r → (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∃ (i : Fin k) (q : Fin r → ℕ),
    y = x i + ∑ j, (q j : ℝ) • w j}

private lemma natGenerated_subset_finitelyGenerated {n k r : ℕ}
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ)) :
    natGeneratedSet x w ⊆ finitelyGeneratedSet x w := by
  classical
  rintro y ⟨i, q, rfl⟩
  refine ⟨Pi.single i 1, fun j ↦ (q j : ℝ), ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases h : a = i <;> simp [Pi.single_apply, h]
  · intro j
    positivity
  · simp [Pi.single_apply]
  · ext a
    simp [Pi.single_apply]

private lemma nat_translate_mem_convexHull {n k r : ℕ}
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ))
    (q : Fin r → ℕ) {y : Fin n → ℝ}
    (hy : y ∈ convexHull ℝ (natGeneratedSet x w)) :
    y + ∑ j, (q j : ℝ) • w j ∈ convexHull ℝ (natGeneratedSet x w) := by
  classical
  let v : Fin n → ℝ := ∑ j, (q j : ℝ) • w j
  let T : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ) :=
    AffineEquiv.constVAdd ℝ (Fin n → ℝ) v
  have hpre : Convex ℝ (T ⁻¹' convexHull ℝ (natGeneratedSet x w)) :=
    (convex_convexHull ℝ (natGeneratedSet x w)).affine_preimage T.toAffineMap
  have hgen : natGeneratedSet x w ⊆
      T ⁻¹' convexHull ℝ (natGeneratedSet x w) := by
    rintro z ⟨i, p, rfl⟩
    apply subset_convexHull ℝ (natGeneratedSet x w)
    refine ⟨i, fun j ↦ p j + q j, ?_⟩
    simp only [T, AffineEquiv.constVAdd_apply, vadd_eq_add]
    rw [show v = ∑ j, (q j : ℝ) • w j by rfl]
    simp only [Nat.cast_add, add_smul]
    rw [Finset.sum_add_distrib]
    abel
  have hz := convexHull_min hgen hpre hy
  simpa [T, v, add_comm] using hz

private lemma real_ray_mem_convexHull {n k r : ℕ}
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ))
    (j : Fin r) (t : ℝ) (ht : 0 ≤ t) {y : Fin n → ℝ}
    (hy : y ∈ convexHull ℝ (natGeneratedSet x w)) :
    y + t • w j ∈ convexHull ℝ (natGeneratedSet x w) := by
  classical
  let a : ℕ := ⌊t⌋₊
  let u : ℝ := t - a
  let q0 : Fin r → ℕ := Pi.single j a
  let q1 : Fin r → ℕ := Pi.single j (a + 1)
  have ha : (a : ℝ) ≤ t := by
    exact Nat.floor_le ht
  have hlt : t < (a : ℝ) + 1 := by
    exact Nat.lt_floor_add_one t
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> dsimp [u] <;> linarith
  have h0 := nat_translate_mem_convexHull x w q0 hy
  have h1 := nat_translate_mem_convexHull x w q1 hy
  have h0' : y + (a : ℝ) • w j ∈
      convexHull ℝ (natGeneratedSet x w) := by
    simpa [q0, Pi.single_apply] using h0
  have h1' : (y + (a : ℝ) • w j) + w j ∈
      convexHull ℝ (natGeneratedSet x w) := by
    have h1'' : y + ((a + 1 : ℕ) : ℝ) • w j ∈
        convexHull ℝ (natGeneratedSet x w) := by
      simpa [q1, Pi.single_apply] using h1
    convert h1'' using 1 <;> push_cast <;> module
  have hi := (convex_convexHull ℝ (natGeneratedSet x w)).add_smul_mem h0' h1' hu
  convert hi using 1 <;> dsimp [u] <;> module

private lemma real_rays_mem_convexHull {n k r : ℕ}
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ))
    (theta : Fin r → ℝ) (htheta : ∀ j, 0 ≤ theta j)
    {y : Fin n → ℝ} (hy : y ∈ convexHull ℝ (natGeneratedSet x w)) :
    y + ∑ j, theta j • w j ∈ convexHull ℝ (natGeneratedSet x w) := by
  classical
  suffices h : ∀ s : Finset (Fin r),
      y + ∑ j ∈ s, theta j • w j ∈ convexHull ℝ (natGeneratedSet x w) by
    simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using hy
  | @insert j s hj ih =>
      have hmem := real_ray_mem_convexHull x w j (theta j) (htheta j) ih
      simpa [Finset.sum_insert, hj, add_assoc, add_left_comm, add_comm] using hmem

/-- The purely formal convexification step in Bertsimas--Tsitsiklis,
Exercise 11.8(c)--(d), p. 525. -/
theorem solution {n k r : ℕ} (x : Fin k → (Fin n → ℝ))
    (w : Fin r → (Fin n → ℝ)) :
    convexHull ℝ
        {y | ∃ (i : Fin k) (q : Fin r → ℕ),
          y = x i + ∑ j, (q j : ℝ) • w j} =
      finitelyGeneratedSet x w := by
  classical
  change convexHull ℝ (natGeneratedSet x w) = finitelyGeneratedSet x w
  apply Set.Subset.antisymm
  · obtain ⟨m, A, b, hpoly⟩ := finitely_generated_is_polyhedron x w
    apply convexHull_min (natGenerated_subset_finitelyGenerated x w)
    rw [hpoly]
    exact polyhedron_convex A b
  · rintro y ⟨lam, theta, hlam, htheta, hsum, rfl⟩
    have hbase : (∑ i, lam i • x i) ∈ convexHull ℝ (natGeneratedSet x w) := by
      apply (convex_convexHull ℝ (natGeneratedSet x w)).sum_mem
      · intro i hi
        exact hlam i
      · simpa using hsum
      · intro i hi
        apply subset_convexHull ℝ (natGeneratedSet x w)
        exact ⟨i, 0, by simp⟩
    exact real_rays_mem_convexHull x w theta htheta hbase
