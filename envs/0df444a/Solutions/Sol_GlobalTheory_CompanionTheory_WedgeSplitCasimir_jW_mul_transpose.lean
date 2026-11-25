-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeSplitCasimir.jW_mul_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:54.006894+00:00
-- url     : https://prove2.me/submissions/dd12aafe-a596-4910-b545-ae2a4ed21928

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialSignRuleQuadratic

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeSplitCasimir
namespace GlobalTheory.CompanionTheory.WedgeSplitCasimir
theorem _root_.solution (n m : ℕ) (J J' : Sub n m) (s s' : Fin n) :
    (jW n m * (jW n m)ᵀ) (J, s) (J', s') =
      if s ∉ J.1 ∧ s' ∉ J'.1 ∧ insert s J.1 = insert s' J'.1 then
        (-1) ^ (J.1.filter fun a => a < s).card * (-1) ^ (J'.1.filter fun a => a < s').card else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, jW]
  by_cases hs : s ∈ J.1
  · simp [hs]
  · have hc : (insert s J.1).card = m + 1 := by rw [Finset.card_insert_of_notMem hs, J.2]
    rw [Finset.sum_eq_single (⟨insert s J.1, hc⟩ : Sub n (m + 1))]
    · by_cases h : s' ∉ J'.1 ∧ insert s J.1 = insert s' J'.1
      · rw [if_pos ⟨hs, rfl⟩, if_pos h, if_pos ⟨hs, h⟩]
      · rw [if_neg h, mul_zero, if_neg (fun h' => h h'.2)]
    · intro I _ hI
      rw [if_neg, zero_mul]
      rintro ⟨_, h⟩
      exact hI (Subtype.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
end GlobalTheory.CompanionTheory.WedgeSplitCasimir
