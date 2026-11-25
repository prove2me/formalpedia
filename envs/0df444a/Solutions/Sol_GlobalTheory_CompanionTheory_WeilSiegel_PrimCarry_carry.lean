-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.carry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:38:05.216306+00:00
-- url     : https://prove2.me/submissions/3fff815f-dc39-4b58-9b96-8a60603830dc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HyperbolicPairUnitaryTransitive
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuasiRefl_exists_unitary_carry


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
open GlobalTheory.CompanionTheory.SW.QuasiRefl
variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}
namespace GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
theorem _root_.solution (hτ : ∀ y, τ (τ y) = y)
    (hcar : ∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1)
    (hH : ∀ i j, τ (H j i) = H i j) (x y : Fin N → A)
    (hxy : hform τ H x x = hform τ H y y) (hβ : IsUnit (hform τ H x x)) :
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ x = y ∧
      ∀ z, hform τ H x z = 0 → hform τ H y z = 0 → (g : Matrix (Fin N) (Fin N) A) *ᵥ z = z := by
  have hfix : τ (hform τ H x x) = hform τ H x x := hform_conj_symm hτ hH x x
  obtain ⟨ε, z, hε, hz⟩ := hcar (hform τ H y x) (hform τ H x x) hβ hfix
  exact exists_unitary_carry A τ hτ N H hH x y ε hxy hβ hε ⟨⟨_, z, hz, (mul_comm z _).trans hz⟩, rfl⟩
end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
