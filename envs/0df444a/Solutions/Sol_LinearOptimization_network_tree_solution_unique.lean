-- Prove2me | solution 1 for LinearOptimization.network_tree_solution_unique
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T04:01:47.830249+00:00
-- url     : https://prove2.me/submissions/68e734a1-7f1e-419d-b187-44317bcb3804

import Definitions.Def_LinearOptimization_TreeSolution
import Theorems.Thm_LinearOptimization_network_incidence_rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.EquivFin

open Matrix

private lemma eq_zero_of_mulVec_of_zero_off_embedding {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Fin n ↪ Fin m)
    (hunit : IsUnit (A.submatrix id B)) (d : Fin m → ℝ)
    (hAd : A.mulVec d = 0) (hd : ∀ j ∉ Set.range B, d j = 0) : d = 0 := by
  classical
  let alpha : Fin n → ℝ := fun i => d (B i)
  have hM : (A.submatrix id B).mulVec alpha = 0 := by
    funext i
    change (∑ k : Fin n, A i (B k) * d (B k)) = 0
    have himage : (∑ k : Fin n, A i (B k) * d (B k)) =
        ∑ j ∈ Finset.univ.image B, A i j * d j := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => B.injective h
    rw [himage]
    have hall : (∑ j ∈ Finset.univ.image B, A i j * d j) =
        ∑ j : Fin m, A i j * d j := by
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
    (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (by simpa using hM)
  funext j
  by_cases hj : j ∈ Set.range B
  · obtain ⟨i, rfl⟩ := hj
    exact congrFun halpha i
  · exact hd j hj

theorem solution {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (bsupply : Fin (n + 1) → ℝ)
    (hloop : LinearOptimization.HasNoSelfLoops arcs)
    (T : Finset (Fin m)) (hT : LinearOptimization.IsTreeArcSet arcs T) :
    ∃! f : Fin m → ℝ,
      (LinearOptimization.truncatedIncidence arcs).mulVec f =
          LinearOptimization.truncatedSupply bsupply ∧
      ∀ k, k ∉ T → f k = 0 := by
  classical
  have hcardT : T.card = n := Nat.add_right_cancel hT.1
  let e : Fin n ≃ T := Fintype.equivOfCardEq (by simp [hcardT])
  let B : Fin n ↪ Fin m :=
    ⟨fun r => (e r).1, fun _ _ h => e.injective (Subtype.ext h)⟩
  let subarcs : Fin n → Fin (n + 1) × Fin (n + 1) := fun r => arcs (B r)
  have hsubloop : LinearOptimization.HasNoSelfLoops subarcs := by
    intro r
    exact hloop (B r)
  have hsubconn : LinearOptimization.IsConnectedNetwork subarcs := by
    intro u v
    have hle : ∀ a b, LinearOptimization.networkAdjacentOn arcs T a b →
        LinearOptimization.networkAdjacent subarcs a b := fun a b hab => by
      obtain ⟨k, hkT, hk⟩ := hab
      let r : Fin n := e.symm ⟨k, hkT⟩
      refine ⟨r, ?_⟩
      have hBr : B r = k := congrArg Subtype.val (e.apply_symm_apply ⟨k, hkT⟩)
      show arcs (B r) = (a, b) ∨ arcs (B r) = (b, a)
      rw [hBr]
      exact hk
    exact Relation.ReflTransGen.mono hle u v (hT.2 u v)
  have hrank := LinearOptimization.network_incidence_rank
    subarcs hsubloop hsubconn
  have hmatrix :
      (LinearOptimization.truncatedIncidence arcs).submatrix id B =
        LinearOptimization.truncatedIncidence subarcs := by
    ext i r
    rfl
  have hunit : IsUnit
      ((LinearOptimization.truncatedIncidence arcs).submatrix id B) := by
    rw [hmatrix]
    exact Matrix.linearIndependent_rows_iff_isUnit.mp (by
      simpa [Matrix.row] using hrank)
  letI : Invertible
      ((LinearOptimization.truncatedIncidence arcs).submatrix id B) :=
    hunit.invertible
  let y : Fin n → ℝ :=
    ((LinearOptimization.truncatedIncidence arcs).submatrix id B)⁻¹.mulVec
      (LinearOptimization.truncatedSupply bsupply)
  let f : Fin m → ℝ := ∑ r : Fin n, Pi.single (B r) (y r)
  have hBy : ((LinearOptimization.truncatedIncidence arcs).submatrix id B).mulVec y =
      LinearOptimization.truncatedSupply bsupply := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
    simp
  have hfEq : (LinearOptimization.truncatedIncidence arcs).mulVec f =
      LinearOptimization.truncatedSupply bsupply := by
    dsimp [f]
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_single]
    funext i
    have hi := congrFun hBy i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
      Function.id_def] at hi
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
    exact hi
  have hRange : Set.range B = {k : Fin m | k ∈ T} := by
    ext k
    constructor
    · rintro ⟨r, rfl⟩
      exact (e r).2
    · intro hk
      refine ⟨e.symm ⟨k, hk⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
  have hfOff : ∀ k, k ∉ T → f k = 0 := by
    intro k hk
    have hkB : k ∉ Set.range B := by simpa [hRange] using hk
    dsimp [f]
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro r _
    have hne : k ≠ B r := by
      intro heq
      exact hkB ⟨r, heq.symm⟩
    simp [Pi.single_apply, hne]
  refine ⟨f, ⟨hfEq, hfOff⟩, ?_⟩
  intro f' hf'
  have hker : (LinearOptimization.truncatedIncidence arcs).mulVec (f' - f) = 0 := by
    rw [Matrix.mulVec_sub, hf'.1, hfEq, sub_self]
  have hoff : ∀ k ∉ Set.range B, (f' - f) k = 0 := by
    intro k hk
    have hkT : k ∉ T := by simpa [hRange] using hk
    simp [hf'.2 k hkT, hfOff k hkT]
  have hzero := eq_zero_of_mulVec_of_zero_off_embedding
    (LinearOptimization.truncatedIncidence arcs) B hunit (f' - f) hker hoff
  exact sub_eq_zero.mp hzero
