-- Prove2me | solution 1 for GlobalTheory.T.ray_class_partial_zeta_continuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:08:20.764933+00:00
-- url     : https://prove2.me/submissions/f2833827-37c8-4b82-9cbb-6e91c3dc0783

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_partial_zeta_continuation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ D : RayData K M, ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : D.G, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = ρ ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → LSeriesSummable (D.cnt c) s ∧ Z s = (s - 1) * LSeries (D.cnt c) s := by
  first | exact @GlobalTheory.Mem.PartialZeta.partial_zeta_continuation | exact GlobalTheory.Mem.PartialZeta.partial_zeta_continuation | (intros; apply GlobalTheory.Mem.PartialZeta.partial_zeta_continuation <;> assumption)
end _root_.GlobalTheory.T
