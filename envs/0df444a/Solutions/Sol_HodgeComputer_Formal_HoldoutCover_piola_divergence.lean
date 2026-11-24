-- Prove2me | solution 1 for HodgeComputer.Formal.HoldoutCover.piola_divergence
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:20:42.042855+00:00
-- url     : https://prove2.me/submissions/52e456b3-b857-4280-a118-aabaaac2cc6a

import Definitions.Def_HodgeComputerFormal_Algebra
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false


/- Source component: RationalPiola -/
section
/-!
Algebraic divergence under a change of coordinates.

These generic identities are intermediate construction lemmas. They do not
assume or assert a certificate for the holdout instance.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

section Products

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

theorem derivation_prod_update (D : Derivation ℤ R R) (s : Finset ι) (f : ι → R) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
    simp only [smul_eq_mul, Finset.mul_sum]
    have hfirst : (∏ j ∈ insert a s, Function.update f a (D (f a)) j) =
        D (f a) * ∏ j ∈ s, f j := by
      rw [Finset.prod_insert ha, Function.update_self,
        Finset.prod_update_of_notMem ha]
    rw [hfirst, add_comm]
    congr 1
    · exact mul_comm _ _
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a ≠ i := by intro h; exact ha (h ▸ hi)
    rw [Finset.prod_insert ha, Function.update_of_ne hai]

end Products

section Determinants

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivation_det_columns (D : Derivation ℤ R R) (M : Matrix ι ι R) :
    D M.det = ∑ i, (M.updateCol i (fun j => D (M j i))).det := by
  classical
  simp only [Matrix.det_apply', map_sum, D.leibniz, D.map_intCast,
    smul_eq_mul, mul_zero, add_zero, derivation_prod_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i
  · subst j; simp
  · simp [Matrix.updateCol, h]

theorem derivation_det_inverse (D : Derivation ℤ R R) (M N : Matrix ι ι R)
    (hMN : M*N = 1) :
    D M.det = M.det * ∑ i, ∑ j, N i j * D (M j i) := by
  rw [derivation_det_columns, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hcol : (fun j => D (M j i)) =
      fun j => ∑ k, (∑ l, N k l * D (M l i)) * M j k := by
    have hh := congrArg (fun v : ι → R => v)
      (Matrix.mulVec_mulVec (fun j => D (M j i)) M N)
    rw [hMN, Matrix.one_mulVec] at hh
    ext j
    have hj := congrFun hh j
    simpa only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm] using hj.symm
  rw [hcol]
  simpa only [smul_eq_mul, mul_comm] using
    (Matrix.det_updateCol_sum M i (fun k => ∑ l, N k l * D (M l i)))

end Determinants

section Divergence

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem fieldDivergence_smul (D : ι → Derivation ℤ K K) (a : K) (v : ι → K) :
    fieldDivergence D (fun i => a*v i) =
      (∑ i, v i * D i a) + a*fieldDivergence D v := by
  simp only [fieldDivergence, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring

omit [DecidableEq ι] in
theorem fieldDivergence_sum {κ : Type*} [Fintype κ]
    (D : ι → Derivation ℤ K K) (v : κ → ι → K) :
    fieldDivergence D (fun i => ∑ k, v k i) = ∑ k, fieldDivergence D (v k) := by
  simp only [fieldDivergence, map_sum]
  rw [Finset.sum_comm]

theorem column_directional
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hNM : N*M = 1)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x) (i : ι) (x : K) :
    ∑ j, M j i * E j x = D i x := by
  simp_rw [chain, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ k, (∑ j, M j i * (N k j * D k x)) =
      (N*M) k i * D k x := by
    intro k
    simp only [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hinner, hNM]
  simp [Matrix.one_apply]

theorem column_divergence
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hMN : M*N = 1) (hdet : M.det ≠ 0)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k)) (i : ι) :
    fieldDivergence E (fun j => M j i) = D i M.det / M.det := by
  rw [derivation_det_inverse (D i) M N hMN]
  unfold fieldDivergence
  simp_rw [chain, mixed]
  rw [Finset.sum_comm]
  field_simp

theorem piola_divergence
    (D E : ι → Derivation ℤ K K) (M N : Matrix ι ι K)
    (hMN : M*N = 1) (hNM : N*M = 1) (hdet : M.det ≠ 0)
    (chain : ∀ j x, E j x = ∑ k, N k j * D k x)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k)) (w : ι → K) :
    fieldDivergence E (fun j => ∑ i, (w i/M.det)*M j i) =
      fieldDivergence D w / M.det := by
  rw [fieldDivergence_sum]
  simp_rw [fieldDivergence_smul,
    column_directional D E M N hNM chain,
    column_divergence D E M N hMN hdet chain mixed]
  unfold fieldDivergence
  conv_rhs => rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, smul_eq_mul]
  field_simp
  ring

end Divergence

end HoldoutConstruction

end
end

open scoped BigOperators in
theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (D E : ι → Derivation ℤ K K)
    (M N : Matrix ι ι K) (hdet : M.det ≠ 0) (hNM : N * M = 1)
    (chain : ∀ j z, E j z = ∑ k, N k j * D k z)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k))
    (u : ι → K) :
    HoldoutConstruction.fieldDivergence E (fun j => ∑ i, (u i / M.det) * M j i) =
      HoldoutConstruction.fieldDivergence D u / M.det := by
  have hMN : M * N = 1 := by
    have hM : M * (M.det⁻¹ • M.adjugate) = 1 := by
      rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hdet, one_smul]
    have hN : N = M.det⁻¹ • M.adjugate := by
      calc N = N * 1 := (Matrix.mul_one N).symm
        _ = N * (M * (M.det⁻¹ • M.adjugate)) := by rw [hM]
        _ = (N * M) * (M.det⁻¹ • M.adjugate) := (Matrix.mul_assoc _ _ _).symm
        _ = M.det⁻¹ • M.adjugate := by rw [hNM, Matrix.one_mul]
    rw [hN, hM]
  exact HoldoutConstruction.piola_divergence D E M N hMN hNM hdet chain mixed u
