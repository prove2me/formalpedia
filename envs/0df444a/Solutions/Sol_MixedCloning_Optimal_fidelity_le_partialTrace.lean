-- Prove2me | solution 1 for MixedCloning.Optimal.fidelity_le_partialTrace
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T02:29:28.799612+00:00
-- url     : https://prove2.me/submissions/fd742630-2bad-4869-8167-d750198e30e4

import Theorems.Thm_FuchsThesis_Broadcast_eq_4_76
import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

section Reindex
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Reindexing a matrix by an equivalence commutes with the square-root functional calculus. -/
lemma fdp_cfc_sqrt_reindex (e : m ≃ n) (A : Matrix m m ℂ) :
    cfc Real.sqrt (reindex e e A) = reindex e e (cfc Real.sqrt A) := by
  let φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ :=
    { (reindexAlgEquiv ℂ ℂ e).toAlgHom with
      map_star' := fun X => by
        change reindex e e (star X) = star (reindex e e X)
        simp [Matrix.star_eq_conjTranspose] }
  have hφ : Continuous φ := continuous_id.matrix_reindex e e
  have hφA : ∀ X, φ X = reindex e e X := fun X => rfl
  by_cases hA : IsSelfAdjoint A
  · have hA' : IsSelfAdjoint (φ A) := hA.map φ
    have h := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ Real.sqrt A
      Real.continuous_sqrt.continuousOn hφ hA hA'
    rw [hφA, hφA] at h
    exact h.symm
  · have hA' : ¬ IsSelfAdjoint (reindex e e A) := by
      intro h
      apply hA
      have h2 : reindex e e (star A) = reindex e e A := by
        have h3 := h.star_eq
        rwa [Matrix.star_eq_conjTranspose, conjTranspose_reindex,
          ← Matrix.star_eq_conjTranspose] at h3
      exact (reindex e e).injective h2
    rw [cfc_apply_of_not_predicate A hA, cfc_apply_of_not_predicate _ hA']
    simp

/-- Trace is invariant under reindexing. -/
lemma fdp_trace_reindex (e : m ≃ n) (A : Matrix m m ℂ) : (reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, reindex_apply, submatrix_apply, diag_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

/-- The root fidelity is invariant under reindexing both arguments by the same equivalence. -/
lemma fdp_rootFidelity_reindex (e : m ≃ n) (X Y : Matrix m m ℂ) :
    QAlgorithms.rootFidelity (reindex e e X) (reindex e e Y) = QAlgorithms.rootFidelity X Y := by
  have hmul : ∀ A B : Matrix m m ℂ, reindex e e A * reindex e e B = reindex e e (A * B) := by
    intro A B
    simp [reindex_apply, submatrix_mul_equiv]
  unfold QAlgorithms.rootFidelity
  rw [fdp_cfc_sqrt_reindex, hmul, hmul, fdp_cfc_sqrt_reindex, fdp_trace_reindex]

/-- The root fidelity is nonnegative: it is the trace of a positive semidefinite square root. -/
lemma fdp_rootFidelity_nonneg (X Y : Matrix n n ℂ) : 0 ≤ QAlgorithms.rootFidelity X Y := by
  unfold QAlgorithms.rootFidelity
  have h : (0 : Matrix n n ℂ) ≤ cfc Real.sqrt (cfc Real.sqrt X * Y * cfc Real.sqrt X) :=
    cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
  have ht := (Matrix.nonneg_iff_posSemidef.mp h).trace_nonneg
  exact (Complex.nonneg_iff.mp ht).1

end Reindex

theorem solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (m : ℕ)
    (X Y : Op (Word (a × b) m)) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    fidelity X Y ≤ fidelity (partialTrace m X) (partialTrace m Y) := by
  let e : Word (a × b) m ≃ Word b m × Word a m :=
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => a) (fun _ => b)).trans (Equiv.prodComm _ _)
  have hpt : ∀ Z : Op (Word (a × b) m),
      WildeQIT.partialTraceLeft (reindex e e Z) = partialTrace m Z := by
    intro Z
    ext i j
    simp only [WildeQIT.partialTraceLeft, partialTrace, Matrix.of_apply, reindex_apply,
      submatrix_apply]
    rfl
  have hX' : (reindex e e X).PosSemidef := by
    rw [reindex_apply]; exact hX.submatrix _
  have hY' : (reindex e e Y).PosSemidef := by
    rw [reindex_apply]; exact hY.submatrix _
  have h := FuchsThesis.Broadcast.eq_4_76 (reindex e e X) (reindex e e Y) hX' hY'
  rw [fdp_rootFidelity_reindex, hpt, hpt] at h
  unfold fidelity
  exact pow_le_pow_left₀ (fdp_rootFidelity_nonneg X Y) h 2
