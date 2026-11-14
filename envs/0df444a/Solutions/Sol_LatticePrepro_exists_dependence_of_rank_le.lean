-- Prove2me | solution 1 for LatticePrepro.exists_dependence_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:27:57.001208+00:00
-- url     : https://prove2.me/submissions/d3dd51b1-f02a-4009-b649-c05d93ba22b8

import Mathlib


namespace LatticePrepro

open Polynomial Matrix

/-- A square matrix of rank `≤ t < ℓ` has linearly dependent first `t + 1` columns. -/
private lemma exists_dependence_of_rank_le {K : Type*} [Field K] {ℓ : ℕ} (A : Matrix (Fin ℓ) (Fin ℓ) K)
    {t : ℕ} (ht : A.rank ≤ t) (htℓ : t + 1 ≤ ℓ) :
    ∃ c : Fin (t + 1) → K, c ≠ 0 ∧ ∀ i : Fin ℓ, ∑ j, c j * A i (Fin.castLE htℓ j) = 0 := by
  classical
  set V := Submodule.span K (Set.range A.col) with hV
  have hfin : Module.finrank K V = A.rank := (Matrix.rank_eq_finrank_span_cols A).symm
  have : Module.Finite K V := Module.Finite.span_of_finite K (Set.finite_range _)
  let v : Fin (t + 1) → V := fun j => ⟨A.col (Fin.castLE htℓ j), Submodule.subset_span ⟨_, rfl⟩⟩
  have hv : ¬ LinearIndependent K v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [hfin, Fintype.card_fin] at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hv
  obtain ⟨g, hg, i₀, hi₀⟩ := hv
  refine ⟨g, fun h => hi₀ (by simp [h]), fun i => ?_⟩
  have := congrArg (fun w : V => (w : Fin ℓ → K) i) hg
  simp only [v, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Matrix.col, Matrix.transpose_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] at this
  exact this

end LatticePrepro

open Polynomial Matrix
theorem solution {K : Type*} [Field K] {ℓ : ℕ} (A : Matrix (Fin ℓ) (Fin ℓ) K)
    {t : ℕ} (ht : A.rank ≤ t) (htℓ : t + 1 ≤ ℓ) :
    ∃ c : Fin (t + 1) → K, c ≠ 0 ∧ ∀ i : Fin ℓ, ∑ j, c j * A i (Fin.castLE htℓ j) = 0 :=
  @LatticePrepro.exists_dependence_of_rank_le K _ ℓ A t ht htℓ
