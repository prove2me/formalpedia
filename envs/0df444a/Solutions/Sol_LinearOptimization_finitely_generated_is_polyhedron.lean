-- Prove2me | solution 1 for LinearOptimization.finitely_generated_is_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T21:39:45.587675+00:00
-- url     : https://prove2.me/submissions/4877630e-d38d-4e92-b932-dfdce80bd906

import Definitions.Def_LinearOptimization_FinitelyGeneratedSet
import Theorems.Thm_LinearOptimization_polyhedron_linear_image
import Mathlib.Algebra.BigOperators.Fin

open Matrix

theorem solution {n k r : ℕ}
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ)) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      LinearOptimization.finitelyGeneratedSet x w =
        LinearOptimization.polyhedron A' b' := by
  classical
  let e : (Fin k ⊕ Fin r) ≃ Fin (Fintype.card (Fin k ⊕ Fin r)) :=
    Fintype.equivFin (Fin k ⊕ Fin r)
  let erow : ((Fin k ⊕ Fin r) ⊕ Bool) ≃
      Fin (Fintype.card ((Fin k ⊕ Fin r) ⊕ Bool)) :=
    Fintype.equivFin ((Fin k ⊕ Fin r) ⊕ Bool)
  let lamRow : Fin (Fintype.card (Fin k ⊕ Fin r)) → ℝ := fun q ↦
    match e.symm q with
    | Sum.inl _ => 1
    | Sum.inr _ => 0
  let D₀ : ((Fin k ⊕ Fin r) ⊕ Bool) →
      (Fin (Fintype.card (Fin k ⊕ Fin r)) → ℝ)
    | Sum.inl q => Pi.single (e q) 1
    | Sum.inr false => lamRow
    | Sum.inr true => -lamRow
  let d₀ : ((Fin k ⊕ Fin r) ⊕ Bool) → ℝ
    | Sum.inl _ => 0
    | Sum.inr false => 1
    | Sum.inr true => -1
  let D : Matrix (Fin (Fintype.card ((Fin k ⊕ Fin r) ⊕ Bool)))
      (Fin (Fintype.card (Fin k ⊕ Fin r))) ℝ :=
    fun q ↦ D₀ (erow.symm q)
  let dRhs : Fin (Fintype.card ((Fin k ⊕ Fin r) ⊕ Bool)) → ℝ :=
    fun q ↦ d₀ (erow.symm q)
  let M : Matrix (Fin n) (Fin (Fintype.card (Fin k ⊕ Fin r))) ℝ := fun j q ↦
    match e.symm q with
    | Sum.inl i => x i j
    | Sum.inr l => w l j
  have sum_reindex (g : Fin (Fintype.card (Fin k ⊕ Fin r)) → ℝ) :
      (∑ q, g q) = ∑ q : (Fin k ⊕ Fin r), g (e q) := by
    exact (Fintype.sum_equiv e (fun q : (Fin k ⊕ Fin r) ↦ g (e q)) g
      (fun _ ↦ rfl)).symm
  have hlamRow (z : Fin (Fintype.card (Fin k ⊕ Fin r)) → ℝ) :
      lamRow ⬝ᵥ z = ∑ i : Fin k, z (e (Sum.inl i)) := by
    simp only [dotProduct]
    rw [sum_reindex]
    change (∑ q : (Fin k ⊕ Fin r), lamRow (e q) * z (e q)) = _
    rw [Fintype.sum_sum_type]
    simp [lamRow]
  have hH (z : Fin (Fintype.card (Fin k ⊕ Fin r)) → ℝ) :
      z ∈ LinearOptimization.polyhedron D dRhs ↔
      (∀ q : (Fin k ⊕ Fin r), 0 ≤ z (e q)) ∧
        (∑ i : Fin k, z (e (Sum.inl i))) = 1 := by
    constructor
    · intro hz
      constructor
      · intro q
        have hq := hz (erow (Sum.inl q))
        simpa [D, dRhs, D₀, Matrix.mulVec, dotProduct, Pi.single_apply] using hq
      · have hlo := hz (erow (Sum.inr false))
        have hhi := hz (erow (Sum.inr true))
        have hlo' : 1 ≤ lamRow ⬝ᵥ z := by
          simpa [D, dRhs, D₀, d₀, Matrix.mulVec] using hlo
        have hhi' : lamRow ⬝ᵥ z ≤ 1 := by
          simpa [D, dRhs, D₀, d₀, Matrix.mulVec, dotProduct] using hhi
        rw [hlamRow] at hlo'
        rw [hlamRow] at hhi'
        linarith
    · rintro ⟨hz, hsum⟩ q
      rw [← erow.apply_symm_apply q]
      rcases hidx : erow.symm q with p | s
      · simp only [hidx]
        simpa [D, dRhs, D₀, Matrix.mulVec, dotProduct, Pi.single_apply] using hz p
      · cases s with
        | false =>
            simp only [hidx]
            simp only [D, dRhs, D₀, erow.symm_apply_apply, Matrix.mulVec]
            change 1 ≤ lamRow ⬝ᵥ z
            rw [hlamRow, hsum]
        | true =>
            simp only [hidx]
            simp only [D, dRhs, D₀, erow.symm_apply_apply, Matrix.mulVec]
            change -1 ≤ (-lamRow) ⬝ᵥ z
            have hneg : (-lamRow) ⬝ᵥ z = -(lamRow ⬝ᵥ z) := by
              simp [dotProduct]
            rw [hneg, hlamRow, hsum]
  have hM (z : Fin (Fintype.card (Fin k ⊕ Fin r)) → ℝ) :
      M.mulVec z =
        (∑ i : Fin k, z (e (Sum.inl i)) • x i) +
        ∑ j : Fin r, z (e (Sum.inr j)) • w j := by
    ext a
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [sum_reindex]
    change (∑ q : (Fin k ⊕ Fin r), M a (e q) * z (e q)) = _
    rw [Fintype.sum_sum_type]
    simp [M, mul_comm]
  have himage : M.mulVec '' LinearOptimization.polyhedron D dRhs =
      LinearOptimization.finitelyGeneratedSet x w := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(fun i ↦ z (e (Sum.inl i))), (fun j ↦ z (e (Sum.inr j))), ?_, ?_, ?_, ?_⟩
      · intro i
        exact (hH z).mp hz |>.1 (Sum.inl i)
      · intro j
        exact (hH z).mp hz |>.1 (Sum.inr j)
      · exact (hH z).mp hz |>.2
      · exact hM z
    · rintro ⟨lam, theta, hlam, htheta, hsum, rfl⟩
      let z : Fin (Fintype.card (Fin k ⊕ Fin r)) → ℝ := fun q ↦
        match e.symm q with
        | Sum.inl i => lam i
        | Sum.inr j => theta j
      have hz : z ∈ LinearOptimization.polyhedron D dRhs := by
        apply (hH z).mpr
        constructor
        · intro q
          cases q with
          | inl i => simpa [z] using hlam i
          | inr j => simpa [z] using htheta j
        · simpa [z] using hsum
      refine ⟨z, hz, ?_⟩
      simpa [z] using hM z
  obtain ⟨m', A', b', hpoly⟩ :=
    LinearOptimization.polyhedron_linear_image D dRhs M
  exact ⟨m', A', b', by rw [← hpoly, himage]⟩
