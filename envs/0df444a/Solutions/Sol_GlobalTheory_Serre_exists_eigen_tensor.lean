-- Prove2me | solution 1 for GlobalTheory.Serre.exists_eigen_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:22.57781+00:00
-- url     : https://prove2.me/submissions/62d5b25a-29a1-40aa-acac-432c8a907ea9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
import Theorems.Thm_GlobalTheory_Serre_mulChar_tmul
import Theorems.Thm_GlobalTheory_Serre_exists_eigen_of_unramified
import Theorems.Thm_GlobalTheory_Serre_exists_eigen_of_projective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Serre.mulChar_tmul

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]
variable {M : Type*} [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]
namespace GlobalTheory.Serre
theorem _root_.solution [Module.Finite O M] [Module.Projective O M]
    {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')]
    [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = algebraMap O R x • l) :
    ∃ s : N ⊗[O'] M →ₗ[R] L ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor L z = algebraMap O' R x • z := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_eigen_of_unramified (R := R) (O := O) (O' := O') (M := M) N
  obtain ⟨j, hj₀, hj₁, hj₂⟩ := exists_eigen_of_projective M (algebraMap O R) i hi
    (fun x n ↦ by rw [(hr _).mp ⟨n, rfl⟩, ← map_smul, algebraMap_smul]) hr
  have hj : ∀ (x : O') z, j ((Algebra.lsmul O O M x).lTensor N z) =
      (Algebra.lsmul O O M x).lTensor L (j z) := fun x z ↦ by
    induction z with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul n m => simp [hj₀]
  refine ⟨j ∘ₗ s, hj₁.comp hs₁, fun z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · rintro ⟨w, rfl⟩ x
    rw [LinearMap.comp_apply, ← hj, (hs₂ _).mp ⟨w, rfl⟩, map_smul]
  · obtain ⟨w, rfl⟩ := (hj₂ z).mpr fun x ↦ by
      rw [IsScalarTower.algebraMap_apply O O' R, ← hz, AlgHom.commutes]
      simp [Module.algebraMap_end_eq_smul_id]
    obtain ⟨v, rfl⟩ := (hs₂ w).mpr fun x ↦ hj₁ (by rw [hj, hz, map_smul])
    exact ⟨v, rfl⟩
end GlobalTheory.Serre
