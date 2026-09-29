-- Prove2me | solution 1 for IsBaseChange.exists_dual_comp_eq_algebraMap_and_sum_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c2b036a7-e690-57b4-ae4d-66fd65240053

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq

set_option autoImplicit false

universe u v w w'

open scoped BigOperators

theorem solution
    {A : Type u} [CommRing A] {A' : Type v} [CommRing A'] [Algebra A A']
    {M : Type w} [AddCommGroup M] [Module A M]
    {M' : Type w'} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']
    (f : M →ₗ[A] M') (hf : IsBaseChange A' f)
    {n : ℕ} (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)) (hxφ : ∀ m : M, ∑ i, φ i m • x i = m) :
    ∃ φ' : Fin n → (M' →ₗ[A'] A'),
      (∀ (i : Fin n) (m : M), φ' i (f m) = algebraMap A A' (φ i m)) ∧
        ∀ m' : M', ∑ i, φ' i m' • f (x i) = m' := by
  let φ' : Fin n → (M' →ₗ[A'] A') := fun i => hf.lift ((Algebra.linearMap A A').comp (φ i))
  have hφ' : ∀ (i : Fin n) (m : M), φ' i (f m) = algebraMap A A' (φ i m) := fun i m =>
    hf.lift_eq _ _
  refine ⟨φ', hφ', fun m' => ?_⟩
  induction m' using hf.inductionOn with
  | zero => simp
  | tmul m =>
      calc ∑ i, φ' i (f m) • f (x i) = ∑ i, f (φ i m • x i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hφ', algebraMap_smul, map_smul]
        _ = f m := by rw [← map_sum, hxφ]
  | smul s m' ih =>
      conv_rhs => rw [← ih]
      simp only [map_smul, smul_eq_mul, Finset.smul_sum, smul_smul]
  | add m₁ m₂ ih₁ ih₂ =>
      conv_rhs => rw [← ih₁, ← ih₂]
      simp only [map_add, add_smul, Finset.sum_add_distrib]

end S_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq
end P2MW
export P2MW.S_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq (solution)
