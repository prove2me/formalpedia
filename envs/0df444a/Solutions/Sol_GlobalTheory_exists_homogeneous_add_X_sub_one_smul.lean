-- Prove2me | solution 1 for GlobalTheory.exists_homogeneous_add_X_sub_one_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:39.750051+00:00
-- url     : https://prove2.me/submissions/8a2829bb-b22e-431d-af61-57e51ea77bd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulEqZeroOfEqXSubOneSmul
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
private lemma X_pow_smul_mem_add_of_mem {j : ℤ} {v : M} (hv : v ∈ ℳ j) (k : ℕ) :
    (X i : MvPolynomial ι R) ^ k • v ∈ ℳ (j + k) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have := _root_.GlobalTheory.X_smul_mem_gr ℳ i (j + k) _ ih
    rw [pow_succ', mul_smul]
    convert this using 2
    push_cast; ring
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
private lemma exists_mem_add_X_sub_one_smul_of_mem_of_le {j n : ℤ} {v : M} (hv : v ∈ ℳ j) (hn : j ≤ n) :
    ∃ y' ∈ ℳ n, ∃ w : M, v = y' + (X i - 1 : MvPolynomial ι R) • w := by
  have hmem := X_pow_smul_mem_add_of_mem ℳ i hv (n - j).toNat
  have e : j + ((n - j).toNat : ℤ) = n := by omega
  rw [e] at hmem
  refine ⟨_, hmem, -(∑ l ∈ Finset.range (n - j).toNat, (X i : MvPolynomial ι R) ^ l) • v, ?_⟩
  rw [neg_smul, smul_neg, smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel
end
end GlobalTheory
end
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι)
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι)
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (y : M) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M, y = y' + (X i - 1 : MvPolynomial ι R) • w := by
  classical
  have hsum : ∀ S : Finset ℤ, ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M,
      ∑ j ∈ S, (decompose ℳ y j : M) = y' + (X i - 1 : MvPolynomial ι R) • w := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨0, fun n _ => ⟨0, zero_mem _, 0, by simp⟩⟩
    | insert a S ha ih =>
      obtain ⟨n₁, hn₁⟩ := ih
      refine ⟨max a n₁, fun n hn => ?_⟩
      obtain ⟨y₁, hy₁, w₁, e₁⟩ :=
        exists_mem_add_X_sub_one_smul_of_mem_of_le ℳ i (decompose ℳ y a).2 (le_of_max_le_left hn)
      obtain ⟨y₂, hy₂, w₂, e₂⟩ := hn₁ n (le_of_max_le_right hn)
      refine ⟨y₁ + y₂, add_mem hy₁ hy₂, w₁ + w₂, ?_⟩
      rw [Finset.sum_insert ha, e₁, e₂, smul_add]
      abel
  obtain ⟨n₀, hn₀⟩ := hsum (decompose ℳ y).support
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨y', hy', w, e⟩ := hn₀ n hn
  exact ⟨y', hy', w, by rw [← e, sum_support_decompose]⟩
end _root_.GlobalTheory
end GlobalTheory
