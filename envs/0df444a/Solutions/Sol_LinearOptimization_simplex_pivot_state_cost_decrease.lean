-- Prove2me | solution 1 for LinearOptimization.simplex_pivot_state_cost_decrease
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T03:52:14.511251+00:00
-- url     : https://prove2.me/submissions/0c5b1fb2-3562-40f1-8ce1-fb48e97b19a1

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_simplex_pivot_basis_change
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Matrix

private lemma eq_zero_of_kernel_of_eq_zero_off_basis {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n)
    (hB : LinearOptimization.IsStdBasis A B) (d : Fin n → ℝ)
    (hAd : A.mulVec d = 0) (hd : ∀ j ∉ Set.range B, d j = 0) : d = 0 := by
  classical
  have hcols : LinearIndependent ℝ (LinearOptimization.basisMatrix A B).col := by
    exact hB
  have hunit : IsUnit (LinearOptimization.basisMatrix A B) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  let alpha : Fin m → ℝ := fun i => d (B i)
  have hBM : (LinearOptimization.basisMatrix A B).mulVec alpha = 0 := by
    funext i
    change (∑ k : Fin m, A i (B k) * d (B k)) = 0
    have himage : (∑ k : Fin m, A i (B k) * d (B k)) =
        ∑ j ∈ Finset.univ.image B, A i j * d j := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => B.injective h
    rw [himage]
    have hall : (∑ j ∈ Finset.univ.image B, A i j * d j) =
        ∑ j : Fin n, A i j * d j := by
      apply Finset.sum_subset (by intro j hj; simp)
      intro j _ hj
      have hjrange : j ∉ Set.range B := by
        intro hr
        obtain ⟨k, rfl⟩ := hr
        exact hj (by simp)
      rw [hd j hjrange, mul_zero]
    rw [hall]
    simpa [Matrix.mulVec, dotProduct] using congrFun hAd i
  have halpha : alpha = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (by simpa using hBM)
  funext j
  by_cases hj : j ∈ Set.range B
  · obtain ⟨i, rfl⟩ := hj
    exact congrFun halpha i
  · exact hd j hj

private lemma simplex_state_is_bfs {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ)
    (hstate : LinearOptimization.IsSimplexState A b B x) :
    LinearOptimization.IsBasicFeasibleSolution
      (LinearOptimization.stdFormSystem A b) x := by
  rcases hstate with ⟨hB, hx, hxB⟩
  have hCset : LinearOptimization.constraintSet
      (LinearOptimization.stdFormSystem A b) =
      LinearOptimization.stdPolyhedron A b := by
    ext y
    constructor
    · intro hy
      constructor
      · funext i
        simpa [LinearOptimization.stdFormSystem, Matrix.mulVec_apply_eq_sum, dotProduct,
          LinearOptimization.LinearConstraint.IsSatisfiedAt] using hy (Sum.inl i)
      · intro j
        simpa [LinearOptimization.stdFormSystem,
          LinearOptimization.LinearConstraint.IsSatisfiedAt, dotProduct,
          Pi.single_apply] using hy (Sum.inr j)
    · rintro ⟨hAy, hynonneg⟩ q
      rcases q with i | j
      · simpa [LinearOptimization.stdFormSystem, Matrix.mulVec_apply_eq_sum, dotProduct,
          LinearOptimization.LinearConstraint.IsSatisfiedAt] using congrFun hAy i
      · simpa [LinearOptimization.stdFormSystem,
          LinearOptimization.LinearConstraint.IsSatisfiedAt, dotProduct,
          Pi.single_apply] using hynonneg j
  have hext : x ∈ Set.extremePoints ℝ
      (LinearOptimization.stdPolyhedron A b) := by
    refine ⟨hx, ?_⟩
    intro y hy z hz hopen
    obtain ⟨a, d, ha, hd, had, hcomb⟩ := hopen
    have hyoff : ∀ j ∉ Set.range B, y j = 0 := by
      intro j hj
      have hxj := hxB j hj
      have hcj := congrFun hcomb j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcj
      have hyj : 0 ≤ y j := hy.2 j
      have hzj : 0 ≤ z j := hz.2 j
      rw [hxj] at hcj
      nlinarith
    have hker : A.mulVec (y - x) = 0 := by
      rw [Matrix.mulVec_sub, hy.1, hx.1, sub_self]
    have hoff : ∀ j ∉ Set.range B, (y - x) j = 0 := by
      intro j hj
      simp [hyoff j hj, hxB j hj]
    exact sub_eq_zero.mp
      (eq_zero_of_kernel_of_eq_zero_off_basis A B hB (y - x) hker hoff)
  have hneC : (LinearOptimization.constraintSet
      (LinearOptimization.stdFormSystem A b)).Nonempty := by
    rw [hCset]
    exact ⟨x, hx⟩
  have hxC : x ∈ LinearOptimization.constraintSet
      (LinearOptimization.stdFormSystem A b) := by simpa [hCset] using hx
  have hextC : x ∈ Set.extremePoints ℝ
      (LinearOptimization.constraintSet (LinearOptimization.stdFormSystem A b)) := by
    simpa [hCset] using hext
  exact ((LinearOptimization.lp_vertex_extreme_bfs_equiv
    (LinearOptimization.stdFormSystem A b) x hneC hxC).out 1 2).mp hextC

private lemma dot_basicDirection_eq_reducedCost {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (j : Fin n) :
    c ⬝ᵥ LinearOptimization.basicDirection A B j =
      LinearOptimization.reducedCost A c B j := by
  classical
  unfold LinearOptimization.basicDirection LinearOptimization.reducedCost
  rw [dotProduct_sub, dotProduct_sum, dotProduct_single]
  simp only [dotProduct_smul, smul_eq_mul, dotProduct_single]
  unfold dotProduct
  ring

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B B' : Fin m ↪ Fin n) (x x' : Fin n → ℝ)
    (hstate : LinearOptimization.IsSimplexState A b B x)
    (hnd : ∀ y, LinearOptimization.IsBasicFeasibleSolution
      (LinearOptimization.stdFormSystem A b) y →
      ¬LinearOptimization.IsStdDegenerateBasicSolution A b y)
    (hpivot : LinearOptimization.IsSimplexPivot A c B x B' x') :
    LinearOptimization.IsSimplexState A b B' x' ∧
      c ⬝ᵥ x' < c ⬝ᵥ x := by
  classical
  rcases hstate with ⟨hB, hx, hxB⟩
  rcases hpivot with ⟨j, ℓ, hpstep, hmin⟩
  rcases hpstep with ⟨hj, hcj, hℓ, hB'ne, hB'ℓ, hx'⟩
  have hbfs : LinearOptimization.IsBasicFeasibleSolution
      (LinearOptimization.stdFormSystem A b) x :=
    simplex_state_is_bfs A b B x ⟨hB, hx, hxB⟩
  have hndx := hnd x hbfs
  have hp := LinearOptimization.simplex_pivot_basis_change
    A b c hA B B' hB x hx hxB hndx j hj hcj ℓ hℓ hmin hB'ne hB'ℓ
  subst x'
  constructor
  · exact ⟨hp.1, hp.2.1, hp.2.2⟩
  · have hbasicPos : ∀ i : Fin m, 0 < x (B i) := by
      intro i
      have hxnonneg := hx.2 (B i)
      apply lt_of_le_of_ne hxnonneg
      intro hzero
      apply hndx
      refine ⟨hbfs.1, ?_⟩
      let R : Set (Fin n) := Set.range B
      let Z : Set (Fin n) := {q | x q = 0}
      have hsub : Rᶜ ⊆ Z := by
        intro q hq
        exact hxB q hq
      have hproper : Rᶜ ⊂ Z := by
        apply Set.ssubset_iff_subset_ne.mpr
        refine ⟨hsub, ?_⟩
        intro heq
        have hBiZ : B i ∈ Z := hzero.symm
        have hBiComp : B i ∈ Rᶜ := heq ▸ hBiZ
        exact hBiComp ⟨i, rfl⟩
      have hcard := Set.ncard_lt_ncard hproper
      have hRcard : R.ncard = m := by
        simpa [R] using Set.ncard_range_of_injective B.injective
      have hcompcard : Rᶜ.ncard = n - m := by
        rw [Set.ncard_compl R, hRcard]
        simp
      simpa [Z, hcompcard] using hcard
    have hθpos : 0 < x (B ℓ) /
        LinearOptimization.pivotColumn A B j ℓ :=
      div_pos (hbasicPos ℓ) hℓ
    rw [dotProduct_add, dotProduct_smul,
      dot_basicDirection_eq_reducedCost A c B j]
    simp only [smul_eq_mul]
    nlinarith
