-- Prove2me | solution 1 for GlobalTheory.T.exists_unit_minor_of_integral_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:20:13.471821+00:00
-- url     : https://prove2.me/submissions/e2e0d5fe-c3c8-4520-b0e9-7ff3d95950c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrixStatement
import Theorems.Thm_GlobalTheory_SatMinor_exists_minor_norm_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] {κ J : Type} [Fintype κ] [DecidableEq κ] [Fintype J] (c : Matrix κ J ℂ_[p]),
  (∀ k i, ‖c k i‖ ≤ 1) →
  (∀ a : κ → ℂ_[p], (∀ i, ‖∑ k, a k * c k i‖ ≤ 1) → ∀ k, ‖a k‖ ≤ 1) →
  ∃ f : κ → J, Function.Injective f ∧ ‖(c.submatrix id f).det‖ = 1 := by
  first | exact @GlobalTheory.SatMinor.exists_minor_norm_one | exact GlobalTheory.SatMinor.exists_minor_norm_one | (intros; apply GlobalTheory.SatMinor.exists_minor_norm_one <;> assumption)
end _root_.GlobalTheory.T
