-- Prove2me | solution 1 for GlobalTheory.SymAlg.algHom_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:13:37.897835+00:00
-- url     : https://prove2.me/submissions/47581420-39af-45e2-8727-00c8f628e025

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
    (φ ψ : SymmetricAlgebra R M →ₐ[R] A) (s : A)
    (h : ∀ m, φ (SymmetricAlgebra.ι R M m) = s * ψ (SymmetricAlgebra.ι R M m)) {d : ℕ}
    {x : SymmetricAlgebra R M} (hx : x ∈ homog R M d) : φ x = s ^ d * ψ x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add, map_add, ihx, ihy, mul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨_, rfl⟩ := hm
    rw [map_mul, map_mul, ih, h, pow_succ]; ring
end GlobalTheory.SymAlg
