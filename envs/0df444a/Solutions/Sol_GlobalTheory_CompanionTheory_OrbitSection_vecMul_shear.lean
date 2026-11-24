-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OrbitSection.vecMul_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:07.040353+00:00
-- url     : https://prove2.me/submissions/4bbb3a2e-5d63-453c-b494-85325b6eebf8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OrbitSection
variable {k : Type} [Field k] {n : ℕ}
namespace GlobalTheory.CompanionTheory.OrbitSection
theorem _root_.solution (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) :
    ζ ᵥ* shear j (ζ j)⁻¹ ζ ξ = ξ := by
  have : ζ ᵥ* vecMulVec (Pi.single j (1 : k)) (ξ - ζ) = (ζ j) • (ξ - ζ) := by
    rw [vecMul_vecMulVec]
    simp
  rw [shear, vecMul_add, vecMul_one, vecMul_smul, this, smul_smul, inv_mul_cancel₀ h0, one_smul]
  abel
end GlobalTheory.CompanionTheory.OrbitSection
