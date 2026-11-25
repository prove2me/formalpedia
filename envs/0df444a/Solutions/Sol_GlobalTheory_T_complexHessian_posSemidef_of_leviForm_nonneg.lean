-- Prove2me | solution 1 for GlobalTheory.T.complexHessian_posSemidef_of_leviForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:57.083587+00:00
-- url     : https://prove2.me/submissions/db831e85-70ed-4d70-b491-c321fabfae2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianPosSemidefOfLeviFormNonneg
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianPosSemidefOfLeviFormNonnegStatement
import Theorems.Thm_GlobalTheory_cHess_posSemidef_of_levi_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (φ : V n → ℝ) (z : V n), ContDiffAt ℝ 2 φ z → (∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → (cHess n (fun v => (φ v : ℂ)) z).PosSemidef := by
  first | exact @GlobalTheory.cHess_posSemidef_of_levi_nonneg | exact GlobalTheory.cHess_posSemidef_of_levi_nonneg | (intros; apply GlobalTheory.cHess_posSemidef_of_levi_nonneg <;> assumption)
end _root_.GlobalTheory.T
