-- Prove2me | solution 1 for GlobalTheory.associatedPrimes_tensor_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:15.915294+00:00
-- url     : https://prove2.me/submissions/f79484d9-fa12-46b2-8728-1620f48906f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_injective_lTensor_residueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
namespace GlobalTheory
theorem _root_.solution (p : Ideal A) [hp : p.IsPrime] :
    associatedPrimes B (M ⊗[A] p.ResidueField) = associatedPrimes B (M ⊗[A] (A ⧸ p)) := by
  refine subset_antisymm ?_
    (associatedPrimes.subset_of_injective (injective_lTensor_residueField p))
  set φ := AlgebraTensorModule.lTensor B M
    (IsScalarTower.toAlgHom A (A ⧸ p) p.ResidueField).toLinearMap with hφ
  have hinj : Function.Injective φ := injective_lTensor_residueField p
  have hsurj : ∀ x : M ⊗[A] p.ResidueField, ∃ r ∉ p, ∃ y, φ y = r • x := fun x ↦ by
    induction x with
    | zero => exact ⟨1, (Ideal.ne_top_iff_one p).1 hp.ne_top, 0, by simp⟩
    | tmul m c =>
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A ⧸ p) c
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hb0 := nonZeroDivisors.ne_zero hb
      refine ⟨b, fun h ↦ hb0 (Ideal.Quotient.eq_zero_iff_mem.2 h), m ⊗ₜ a, ?_⟩
      have : algebraMap (A ⧸ p) p.ResidueField (Ideal.Quotient.mk p b) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (A ⧸ p) p.ResidueField)).2 hb0
      rw [← tmul_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField,
        Ideal.Quotient.algebraMap_eq, mul_div_cancel₀ _ this]
      simp [hφ]
    | add x y hx hy =>
      obtain ⟨r, hr, x', hx'⟩ := hx
      obtain ⟨s, hs, y', hy'⟩ := hy
      refine ⟨r * s, p.primeCompl.mul_mem hr hs, s • x' + r • y', ?_⟩
      rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hx', hy', smul_add,
        smul_smul, smul_smul, mul_comm s r]
  have hreg : ∀ r ∉ p, ∀ x : M ⊗[A] p.ResidueField, r • x = 0 → x = 0 := fun r hr x hx ↦ by
    have h1 : Function.Injective (r • LinearMap.id : p.ResidueField →ₗ[A] p.ResidueField) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      simpa [Algebra.smul_def, hr] using hz
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := M) _ h1 (by simpa using hx)
  rintro q ⟨hq, x, hx⟩
  obtain ⟨r, hr, y, hy⟩ := hsurj x
  refine ⟨hq, y, ?_⟩
  rw [hx]
  congr 1
  ext b
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  rw [← map_eq_zero_iff φ hinj, map_smul, hy, smul_comm]
  exact ⟨fun h ↦ by rw [h, smul_zero], hreg r hr _⟩
end GlobalTheory
