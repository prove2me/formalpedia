-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCount.addSet_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:04.00022+00:00
-- url     : https://prove2.me/submissions/2cda0e84-d81c-421e-bec0-480cf1a23195

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CountingBound
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCount_addSet_insert

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
theorem _root_.solution {n : ℕ} (μ : Fin n → ℝ) (J I : Finset (Fin n)) (s : Fin n) :
    addSet μ J + Pi.single s 1 = addSet μ I ↔ s ∉ J ∧ I = insert s J := by
  constructor
  · intro h
    have hs : s ∉ J := by
      intro hs
      have := congrFun h s
      simp only [addSet, Pi.add_apply, Pi.single_eq_same, if_pos hs] at this
      split_ifs at this <;> linarith
    refine ⟨hs, ?_⟩
    rw [addSet_insert μ J s hs] at h
    ext a
    have := congrFun h a
    simp only [addSet, add_right_inj] at this
    by_cases h1 : a ∈ I <;> by_cases h2 : a ∈ insert s J <;> simp_all
  · rintro ⟨hs, rfl⟩
    exact addSet_insert μ J s hs
end GlobalTheory.CompanionTheory.ZuckCount
