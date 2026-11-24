-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.lam_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:36.353305+00:00
-- url     : https://prove2.me/submissions/f1f9fbab-2e91-4a05-a30a-3fe8a099608f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_lam_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {G : Type*} [Group G] [Fintype G]
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution (H : Subgroup G) (lam : G → ℂ)
    (hm : ∀ a ∈ H, ∀ b ∈ H, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ H, lam a ≠ 0)
    (a : G) (ha : a ∈ H) : lam a⁻¹ = (lam a)⁻¹ := by
  have h := hm a ha a⁻¹ (H.inv_mem ha)
  rw [mul_inv_cancel, lam_one H lam hm hne] at h
  exact eq_inv_of_mul_eq_one_right h.symm
end GlobalTheory.CompanionTheory.RootExch
