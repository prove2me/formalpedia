-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.lam_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:38.163662+00:00
-- url     : https://prove2.me/submissions/15b612ef-9fe1-49ab-9dd1-02fa0bd5e7ad

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange

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
    (hm : ∀ a ∈ H, ∀ b ∈ H, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ H, lam a ≠ 0) : lam 1 = 1 := by
  have h := hm 1 H.one_mem 1 H.one_mem
  have h0 := hne 1 H.one_mem
  simp only [mul_one] at h
  exact (mul_right_inj' h0).1 (by rw [mul_one]; exact h.symm)
end GlobalTheory.CompanionTheory.RootExch
