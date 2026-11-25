-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.apply_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:16:50.608801+00:00
-- url     : https://prove2.me/submissions/12f4ca50-c610-4ef1-9d33-a2f54ac2c843

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_exists_sum_zpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.LocalField
namespace IsCharacter
theorem _root_.solution {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) {N : ℕ} [NeZero N]
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hN : orderOf s ∣ N) :
    χ s ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  obtain ⟨m, β, hβ, h⟩ := hχ.exists_sum_zpow s
  have hβN : ∀ ψ, β ψ ^ N = 1 := by
    intro ψ
    obtain ⟨k, hk⟩ := hN
    rw [hk, pow_mul, hβ, one_pow]
  have hmem : ∀ ψ, β ψ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
    intro ψ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (hβN ψ)
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _
  have h1 : χ s = ∑ ψ ∈ irrChars (Subgroup.zpowers s), (m ψ : ℂ) * β ψ := by
    simpa using h 1
  rw [h1]
  exact Subalgebra.sum_mem _ fun ψ _ ↦ Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem ψ)
end IsCharacter
end GroundTheory.LocalField
