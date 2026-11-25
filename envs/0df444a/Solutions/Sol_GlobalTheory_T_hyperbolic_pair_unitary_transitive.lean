-- Prove2me | solution 1 for GlobalTheory.T.hyperbolic_pair_unitary_transitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:31.517712+00:00
-- url     : https://prove2.me/submissions/b9778c64-1211-4611-a4d3-62a36a5e09a5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HyperbolicPairUnitaryTransitive
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HyperbolicPairUnitaryTransitiveStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_exists_unitary_carry_primitive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) → (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) → ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) → ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 → hform τ H y y = 0 → ∑ k, a k * y k = 1 → ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | exact GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive <;> assumption)
end _root_.GlobalTheory.T
