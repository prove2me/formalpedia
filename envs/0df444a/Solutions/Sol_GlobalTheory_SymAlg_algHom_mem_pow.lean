-- Prove2me | solution 1 for GlobalTheory.SymAlg.algHom_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:51.138804+00:00
-- url     : https://prove2.me/submissions/8d2d0640-6ee4-4edb-a632-93feccad1c2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open scoped DirectSum
open GlobalTheory
open GlobalTheory.SymAlg
variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
namespace GlobalTheory.SymAlg
theorem _root_.solution {A : Type*} [CommRing A] [Algebra R A]
    (φ : SymmetricAlgebra R M →ₐ[R] A) (P : Submodule R A)
    (h : ∀ m, φ (SymmetricAlgebra.ι R M m) ∈ P) {d : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ homog R M d) : φ x ∈ P ^ d := by
  have h1 : (LinearMap.range (SymmetricAlgebra.ι R M)).map φ.toLinearMap ≤ P := by
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    exact h m
  have h2 := Submodule.map_pow (LinearMap.range (SymmetricAlgebra.ι R M)) φ d
  have h3 : φ x ∈ ((LinearMap.range (SymmetricAlgebra.ι R M)) ^ d).map φ.toLinearMap :=
    ⟨x, hx, rfl⟩
  rw [h2] at h3
  exact pow_le_pow_left' h1 d h3
end GlobalTheory.SymAlg
