-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BlockIwahoriUML.iwahori_block_upper_levi_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:53:22.623026+00:00
-- url     : https://prove2.me/submissions/b1ff69a1-7969-4fd4-9858-e69a68fa7a72

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower
import Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
namespace GlobalTheory.CompanionTheory.BlockIwahoriUML
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (β : Fin N → ℕ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 → (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Monotone β → ∀ g ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ nm ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ l ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ np ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, (∀ i j, β i ≤ β j → (nm : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ (∀ i j, β i ≠ β j → (l : Matrix (Fin N) (Fin N) k) i j = 0) ∧ (∀ i j, β j ≤ β i → (np : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) ∧ g = np * l * nm := by
  intro k _ _ _ _ N ϖ m β _ hϖ _ hm hβ g hg
  have hr : ValuativeRel.valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' hϖ (by omega)
  exact factor (ValuativeRel.valuation k) hr β hβ g hg
end GlobalTheory.CompanionTheory.BlockIwahoriUML
