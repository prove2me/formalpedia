-- Prove2me | solution 1 for MayersQBC.cheat_ge_fidelity
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:00:11.284359+00:00
-- url     : https://prove2.me/submissions/1effe368-1a06-42a9-b223-55fe6259da72

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Theorems.Thm_MayersQBC_uhlmann_purification
import Theorems.Thm_MayersQBC_effectProb_ge_normSq_inner
import Theorems.Thm_QAlgorithms_DeWolf_perfectBitCommitment_impossible
open QAlgorithms

open scoped Matrix ComplexConjugate

namespace MayersQBCCheatAux

/-- Coordinates of `(U ⊗ I) ψ`. -/
lemma act_kronecker_one_apply {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (U : Matrix A A ℂ) (ψ : EuclideanSpace ℂ (A × B)) (a : A) (b : B) :
    act (Matrix.kronecker U (1 : Matrix B B ℂ)) ψ (a, b) = ∑ a', U a a' * ψ (a', b) := by
  simp only [act, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, PiLp.toLp_apply]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'
    simp [Ne.symm hb']
  · simp

/-- The perfectly concealing case on arbitrary finite types, transported from the platform theorem
`QAlgorithms.DeWolf.perfectBitCommitment_impossible` (stated on `Fin dA × Fin dB`) along
`Fintype.equivFin`. -/
lemma perfect_general {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (phi0 phi1 : EuclideanSpace ℂ (A × B)) (h0 : IsState phi0) (h1 : IsState phi1)
    (hconceal : traceLeft (pureDensity phi0) = traceLeft (pureDensity phi1)) :
    ∃ U ∈ Matrix.unitaryGroup A ℂ, act (Matrix.kronecker U (1 : Matrix B B ℂ)) phi0 = phi1 := by
  classical
  set eA := Fintype.equivFin A
  set eB := Fintype.equivFin B
  let e : A × B ≃ Fin (Fintype.card A) × Fin (Fintype.card B) := eA.prodCongr eB
  let r := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  have hr_apply : ∀ (ψ : EuclideanSpace ℂ (A × B)) (i : Fin (Fintype.card A))
      (j : Fin (Fintype.card B)), r ψ (i, j) = ψ (eA.symm i, eB.symm j) := by
    intro ψ i j
    rfl
  have hr_state : ∀ ψ : EuclideanSpace ℂ (A × B), IsState ψ → IsState (r ψ) := by
    intro ψ hψ
    show ‖r ψ‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact hψ
  have hr_tr : ∀ ψ : EuclideanSpace ℂ (A × B),
      traceLeft (pureDensity (r ψ)) = (traceLeft (pureDensity ψ)).submatrix eB.symm eB.symm := by
    intro ψ
    ext j j'
    simp only [traceLeft, pureDensity, Matrix.of_apply, Matrix.submatrix_apply, hr_apply]
    exact Fintype.sum_equiv eA.symm _ _ (fun i => rfl)
  obtain ⟨U', hU', hact⟩ := QAlgorithms.DeWolf.perfectBitCommitment_impossible _ _ (r phi0)
    (r phi1) (hr_state _ h0) (hr_state _ h1) (by rw [hr_tr, hr_tr, hconceal])
  refine ⟨U'.submatrix eA eA, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hU' ⊢
    rw [Matrix.star_eq_conjTranspose] at hU' ⊢
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU',
      Matrix.submatrix_one_equiv]
  · ext ⟨a, b⟩
    have h := congrArg (fun v : EuclideanSpace ℂ (Fin (Fintype.card A) × Fin (Fintype.card B)) =>
      v (eA a, eB b)) hact
    simp only at h
    rw [act_kronecker_one_apply, hr_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      at h
    rw [act_kronecker_one_apply, ← h]
    refine Fintype.sum_equiv eA _ _ (fun a' => ?_)
    simp [hr_apply]

end MayersQBCCheatAux

open MayersQBCCheatAux in
theorem solution {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ψ0 ψ1 : EuclideanSpace ℂ (A × B)) (h0 : IsState ψ0) (h1 : IsState ψ1)
    (E : Matrix (A × B) (A × B) ℂ) (hE : IsEffect E) (hcorrect : effectProb E (pureDensity ψ1) = 1) :
    ∃ U ∈ Matrix.unitaryGroup A ℂ,
      rootFidelity (traceLeft (pureDensity ψ0)) (traceLeft (pureDensity ψ1)) ^ 2 ≤
        effectProb E (pureDensity (act (Matrix.kronecker U (1 : Matrix B B ℂ)) ψ0)) := by
  -- Uhlmann (attained, on Alice's given system): a purification `ψ01` of Bob's state `ρ_B(ψ0)`
  -- with `⟨ψ01|ψ1⟩ = √F`.
  obtain ⟨ψ01, hst, hred, hov⟩ := MayersQBC.uhlmann_purification ψ0 ψ1 h0 h1
  -- `ψ01` and `ψ0` have the same reduced state on Bob's side, so a unitary on Alice's side
  -- takes `ψ0` to `ψ01` (the perfectly concealing case).
  obtain ⟨U, hU, hUψ⟩ := perfect_general ψ0 ψ01 h0 hst hred.symm
  refine ⟨U, hU, ?_⟩
  rw [hUψ]
  -- the effect accepting `ψ1` with certainty accepts `ψ01` with probability `≥ |⟨ψ01|ψ1⟩|² = F`
  have key := MayersQBC.effectProb_ge_normSq_inner E hE ψ1 ψ01 h1 hcorrect
  rw [hov, Complex.norm_real, Real.norm_eq_abs, sq_abs] at key
  exact key
