-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OrbitSection.coe_orbitSection_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:54:13.299405+00:00
-- url     : https://prove2.me/submissions/a912f01b-776a-4691-b19c-de737efe3d06

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
theorem _root_.solution (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    ((orbitSection j ζ ξ)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ).val = shear j (-(ξ j)⁻¹) ζ ξ := by
  rw [orbitSection, dif_pos ⟨h0, h1⟩]
  rfl
end GlobalTheory.CompanionTheory.OrbitSection
