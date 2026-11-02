-- Prove2me | solution 1 for MayersBC.exists_unitary_inner_eq_rootFidelity
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:29:13.360891+00:00
-- url     : https://prove2.me/submissions/bea2e525-0eb0-4b4a-97b4-8e65aa77ced1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_MayersBC_IsConcealing
import Theorems.Thm_MayersQBC_uhlmann_purification
import Theorems.Thm_QAlgorithms_DeWolf_perfectBitCommitment_impossible
import Theorems.Thm_MayersBC_rootFidelity_bounds_of_concealing
open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

namespace MayersBCUnitaryAux

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

/-- The reduced state on Bob's side of a unit vector is a density matrix. -/
lemma traceLeft_pureDensity_isDensityMatrix {A B : Type} [Fintype A] [Fintype B]
    (ψ : EuclideanSpace ℂ (A × B)) (hψ : IsState ψ) :
    IsDensityMatrix (traceLeft (pureDensity ψ)) := by
  let C : Matrix B A ℂ := Matrix.of fun b a => ψ (a, b)
  have hC : traceLeft (pureDensity ψ) = C * Cᴴ := by
    ext b b'
    simp [C, traceLeft, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine ⟨hC ▸ Matrix.posSemidef_self_mul_conjTranspose C, ?_⟩
  -- the trace is `‖ψ‖² = 1`
  have hn : ‖ψ‖ ^ 2 = 1 := by rw [(hψ : ‖ψ‖ = 1), one_pow]
  rw [EuclideanSpace.norm_sq_eq] at hn
  have : (traceLeft (pureDensity ψ)).trace = ((∑ x : A × B, ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, traceLeft, pureDensity, Matrix.of_apply,
      Fintype.sum_prod_type]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [this, hn]
  simp

end MayersBCUnitaryAux

open MayersBCUnitaryAux MayersBC in
theorem solution {A ι : Type} [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι] (ρ0 ρ1 : Matrix ι ι ℂ) (ψ0 ψ1 : EuclideanSpace ℂ (A × ι))
    (hψ0 : IsState ψ0) (hψ1 : IsState ψ1)
    (hp0 : traceLeft (pureDensity ψ0) = ρ0) (hp1 : traceLeft (pureDensity ψ1) = ρ1) (ε : ℝ)
    (hc : IsConcealing ε ρ0 ρ1) :
    (∃ U ∈ Matrix.unitaryGroup A ℂ,
      inner ℂ (act (Matrix.kronecker U (1 : Matrix ι ι ℂ)) ψ0) ψ1 = ((rootFidelity ρ0 ρ1 : ℝ) : ℂ)) ∧
      1 - 2 * ε ≤ rootFidelity ρ0 ρ1 := by
  refine ⟨?_, ?_⟩
  · -- Uhlmann (attained, on Alice's system) and the perfectly concealing case
    obtain ⟨ψ01, hst, hred, hov⟩ := MayersQBC.uhlmann_purification ψ0 ψ1 hψ0 hψ1
    obtain ⟨U, hU, hUψ⟩ := perfect_general ψ0 ψ01 hψ0 hst hred.symm
    refine ⟨U, hU, ?_⟩
    rw [hUψ, hov, hp0, hp1]
  · -- Bob's criterion bounds the root fidelity from below
    have hd0 : IsDensityMatrix ρ0 := hp0 ▸ traceLeft_pureDensity_isDensityMatrix ψ0 hψ0
    have hd1 : IsDensityMatrix ρ1 := hp1 ▸ traceLeft_pureDensity_isDensityMatrix ψ1 hψ1
    exact (rootFidelity_bounds_of_concealing ρ0 ρ1 hd0 hd1 ε hc).1
