-- Prove2me | solution 1 for GlobalTheory.KTypeSteps.nsq_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:45.862147+00:00
-- url     : https://prove2.me/submissions/f94a8629-1798-40a4-aa4b-45e1e523b8cb

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_KtypesWithinSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.KTypeSteps
namespace GlobalTheory.KTypeSteps
theorem _root_.solution {n : ℕ} {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  have h : ∀ c, root a b c * root a b c =
      (if c = a then (1 : ℝ) else 0) + (if c = b then (1 : ℝ) else 0) := by
    intro c
    by_cases h1 : c = a
    · subst h1
      simp [root, hab]
    · by_cases h2 : c = b
      · subst h2
        simp [root, h1]
      · simp [root, h1, h2]
  simp only [nsq, dot, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num
end GlobalTheory.KTypeSteps
