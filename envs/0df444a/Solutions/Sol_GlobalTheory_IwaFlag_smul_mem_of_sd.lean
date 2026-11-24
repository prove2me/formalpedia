-- Prove2me | solution 1 for GlobalTheory.IwaFlag.smul_mem_of_sd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:45.058053+00:00
-- url     : https://prove2.me/submissions/e6b92e84-2606-4d67-a25d-d55f3af934f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IwaFlag
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}
namespace GlobalTheory.IwaFlag
theorem _root_.solution (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hM₁ : ∀ y ∈ M, ε • y = y)
    (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O)) {o : R} (ho : o ∈ O) {y : V} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM₂ _ (by rw [smul_comm, hM₁ y hy])).2 fun x hx => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact hmul _ ho _ ((hM₂ y (hM₁ y hy)).1 hy x hx)
end GlobalTheory.IwaFlag
