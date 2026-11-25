-- Prove2me | solution 1 for GlobalTheory.X_sub_one_smul_graded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:19.283548+00:00
-- url     : https://prove2.me/submissions/ce5d0d16-3d7d-40fa-804a-c48d1add0a1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Theorems.Thm_GlobalTheory_exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul
import Theorems.Thm_GlobalTheory_exists_homogeneous_add_X_sub_one_smul
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_X_smul_mem_gr
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id


section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
namespace GlobalTheory
open GradedHilbert
section
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι)
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma decompose_X_smul_add_one (y : M) (m : ℤ) :
    (decompose ℳ ((X i : MvPolynomial ι R) • y) (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ y m : M) := by
  classical
  have key : ∀ j, (decompose ℳ ((X i : MvPolynomial ι R) • (decompose ℳ y j : M)) (m + 1) : M)
      = if j = m then (X i : MvPolynomial ι R) • (decompose ℳ y m : M) else 0 := by
    intro j
    have hmem := _root_.GlobalTheory.X_smul_mem_gr ℳ i j _ (decompose ℳ y j).2
    split_ifs with hj
    · subst hj; exact decompose_of_mem_same ℳ hmem
    · exact decompose_of_mem_ne ℳ hmem (by omega)
  conv_lhs => rw [← sum_support_decompose ℳ y]
  rw [Finset.smul_sum, decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum]
  simp only [key]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 h]; simp
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma decompose_X_sub_one_smul_add_one (w : M) (m : ℤ) :
    (decompose ℳ ((X i - 1 : MvPolynomial ι R) • w) (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ w m : M) - (decompose ℳ w (m + 1) : M) := by
  rw [sub_smul, one_smul, decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
    decompose_X_smul_add_one]
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_decompose_eq_zero_of_lt (y : M) :
    ∃ N : ℤ, ∀ j < N, (decompose ℳ y j : M) = 0 := by
  classical
  obtain ⟨N, hN⟩ := (decompose ℳ y).support.bddBelow
  refine ⟨N, fun j hj => ?_⟩
  have : j ∉ (decompose ℳ y).support := fun h => by have := hN h; omega
  simp [DFinsupp.notMem_support_iff.1 this]
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma eq_zero_of_X_smul_recurrence_of_vanish_below {g : ℤ → M} {N c : ℤ} (hN : ∀ j < N, g j = 0)
    (hrec : ∀ m < c, g (m + 1) = (X i : MvPolynomial ι R) • g m) : g c = 0 := by
  have key : ∀ k : ℕ, g c = (X i : MvPolynomial ι R) ^ k • g (c - k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : c - (k : ℤ) = c - ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [ih, e, hrec _ (by omega), ← mul_smul, ← pow_succ]
  rw [key (c - N + 1).toNat, hN _ (by omega), smul_zero]
end
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
include ℳ in
private lemma eq_zero_of_X_sub_one_smul_eq_zero {y : M}
    (hy : (X i - 1 : MvPolynomial ι R) • y = 0) : y = 0 := by
  classical
  have hrec : ∀ m, (decompose ℳ y (m + 1) : M) = (X i : MvPolynomial ι R) • (decompose ℳ y m : M) := by
    intro m
    have := decompose_X_sub_one_smul_add_one ℳ i y m
    rw [hy, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at this
    exact (sub_eq_zero.1 this.symm).symm
  obtain ⟨N, hN⟩ := exists_decompose_eq_zero_of_lt ℳ y
  have hall : ∀ c, (decompose ℳ y c : M) = 0 := fun c =>
    eq_zero_of_X_smul_recurrence_of_vanish_below i (g := fun m => (decompose ℳ y m : M)) hN (fun m _ => hrec m)
  rw [← sum_support_decompose ℳ y]
  exact Finset.sum_eq_zero (fun j _ => hall j)
end GlobalTheory
end
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory
open GradedHilbert
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), (∀ y : M, (X i - 1 : MvPolynomial ι R) • y = 0 → y = 0) ∧ (∀ (n : ℤ) (z w : M), z ∈ ℳ n → z = (X i - 1 : MvPolynomial ι R) • w → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z = 0) ∧ (∀ y : M, ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M, y = y' + (X i - 1 : MvPolynomial ι R) • w) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  exact ⟨fun y hy => eq_zero_of_X_sub_one_smul_eq_zero ℳ i hy,
    fun n z w hz h => _root_.GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul ℳ i hz h,
    fun y => _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul ℳ i y⟩
end _root_.GlobalTheory
end GlobalTheory
