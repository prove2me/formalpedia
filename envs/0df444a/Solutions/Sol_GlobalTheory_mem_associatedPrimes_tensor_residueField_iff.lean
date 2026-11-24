-- Prove2me | solution 1 for GlobalTheory.mem_associatedPrimes_tensor_residueField_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:20:04.020409+00:00
-- url     : https://prove2.me/submissions/fdc30d19-4f33-42d4-b6e9-d91cb234e866

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul

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
theorem _root_.solution (p : Ideal A) [p.IsPrime] (q : Ideal B) :
    q ∈ associatedPrimes B (B ⊗[A] p.ResidueField) ↔
      ∃ Q ∈ associatedPrimes (p.Fiber B) (p.Fiber B),
        Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) = q := by
  let e := Algebra.TensorProduct.comm A B p.ResidueField
  have key : ∀ (b : B) (x : B ⊗[A] p.ResidueField),
      (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) b ∈
        ((⊥ : Submodule (p.Fiber B) (p.Fiber B)).colon {e x}).radical ↔
      b ∈ ((⊥ : Submodule B (B ⊗[A] p.ResidueField)).colon {x}).radical := fun b x ↦ by
    simp only [Ideal.mem_radical_iff, Submodule.mem_colon_singleton, Submodule.mem_bot, ← map_pow]
    refine exists_congr fun n ↦ ?_
    rw [← map_eq_zero_iff e e.injective, Algebra.smul_def (b ^ n) x, map_mul]
    rfl
  constructor
  · rintro ⟨hq, x, hx⟩
    refine ⟨((⊥ : Submodule (p.Fiber B) (p.Fiber B)).colon {e x}).radical, ⟨⟨?_, ?_⟩, e x, rfl⟩, ?_⟩
    · rw [Ideal.ne_top_iff_one, ← map_one (Algebra.TensorProduct.includeRight :
        B →ₐ[A] p.Fiber B), key, ← hx, ← Ideal.ne_top_iff_one]
      exact hq.ne_top
    · have aux : ∀ y : p.Fiber B, ∃ u : p.Fiber B, IsUnit u ∧ ∃ b : B,
          u * y = (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) b := fun y ↦ by
        obtain ⟨r, hr, s, h⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p y
        refine ⟨algebraMap A _ r, ?_, s, by rw [← Algebra.smul_def, h]; rfl⟩
        rw [IsScalarTower.algebraMap_apply A p.ResidueField (p.Fiber B)]
        exact (IsUnit.mk0 _ (by simpa using hr)).map _
      intro y z hyz
      obtain ⟨u, hu, b, hb⟩ := aux y
      obtain ⟨u', hu', b', hb'⟩ := aux z
      rw [← Ideal.unit_mul_mem_iff_mem _ (x := y) hu, ← Ideal.unit_mul_mem_iff_mem _ (x := z) hu',
        hb, hb', key, key, ← hx]
      refine hq.mem_or_mem ?_
      rw [hx, ← key, map_mul, ← hb, ← hb', mul_mul_mul_comm]
      exact Ideal.mul_mem_left _ _ hyz
    · ext b
      rw [Ideal.mem_comap, key, hx]
  · rintro ⟨Q, ⟨hQ, x, hx⟩, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective x
    refine ⟨Ideal.comap_isPrime _ _, x, ?_⟩
    ext b
    rw [Ideal.mem_comap, ← key, ← hx]
end GlobalTheory
