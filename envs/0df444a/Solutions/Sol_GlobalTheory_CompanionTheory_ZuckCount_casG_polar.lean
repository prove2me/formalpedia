-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCount.casG_polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:16:08.807309+00:00
-- url     : https://prove2.me/submissions/492270b1-e9a4-4903-96e7-b232c358efee

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CountingBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCount
namespace GlobalTheory.CompanionTheory.ZuckCount
theorem _root_.solution {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    casG (addSet μ J) + casG (μ + Pi.single s 1) + (2 - casG μ) - casG (addSet μ J + Pi.single s 1)
      = if s ∈ J then 0 else 2 := by
  have h : ∑ a, ((addSet μ J a) ^ 2 + ((μ + Pi.single s 1 : Fin n → ℝ) a) ^ 2 - μ a ^ 2
      - ((addSet μ J + Pi.single s 1 : Fin n → ℝ) a) ^ 2) = if s ∈ J then -2 else 0 := by
    rw [Finset.sum_eq_single s]
    · simp only [addSet, Pi.add_apply, Pi.single_eq_same]
      split_ifs <;> ring
    · intro b _ hb
      simp only [addSet, Pi.add_apply, Pi.single_eq_of_ne hb]
      ring
    · simp
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  unfold casG
  split_ifs at h ⊢ <;> linarith
end GlobalTheory.CompanionTheory.ZuckCount
