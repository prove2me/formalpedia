-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OrbitSection.shear_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:05.390836+00:00
-- url     : https://prove2.me/submissions/f219a25a-9b13-484c-ad7c-592f389c8742

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
theorem _root_.solution (j : Fin n) (c : k) (ζ : Fin n → k) : shear j c ζ ζ = 1 := by
  simp [shear]
end GlobalTheory.CompanionTheory.OrbitSection
