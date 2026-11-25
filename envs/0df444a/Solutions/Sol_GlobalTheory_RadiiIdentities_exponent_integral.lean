-- Prove2me | solution 1 for GlobalTheory.RadiiIdentities.exponent_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:58.162434+00:00
-- url     : https://prove2.me/submissions/743fafdb-d557-4a88-a4c8-42c4249a286a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
import Theorems.Thm_GlobalTheory_RadiiIdentities_sub_one_pos
import Theorems.Thm_GlobalTheory_RadiiIdentities_sq_sub_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory
open GlobalTheory.RadiiIdentities
namespace GlobalTheory.RadiiIdentities
theorem _root_.solution : Formalism.L2.FormalSeriesBounds.EInt := by
  intro l i hl hi
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have hsq : ((l : ℝ) ^ 2 - 1) ≠ 0 := by
    rw [sq_sub_one_eq]
    have : (0 : ℝ) < (l : ℝ) + 1 := by linarith
    positivity
  constructor
  · simp only [gam, rho]
    field_simp
  · obtain ⟨k, rfl⟩ := hi
    have hk : (2 * k + 1 - 1) / 2 = k := by omega
    have hne : ((l : ℝ) ^ 2) ≠ 1 := by
      intro h
      apply hsq
      rw [h]
      ring
    simp only [expE, hk, Ereal, rho]
    push_cast
    rw [geom_sum_eq hne]
    field_simp
    ring
end GlobalTheory.RadiiIdentities
