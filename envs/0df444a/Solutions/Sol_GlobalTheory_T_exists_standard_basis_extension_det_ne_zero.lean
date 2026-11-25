-- Prove2me | solution 1 for GlobalTheory.T.exists_standard_basis_extension_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:19:13.895402+00:00
-- url     : https://prove2.me/submissions/9992438a-cae4-40aa-83c8-ca6e4bf26d84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStandardBasisExtensionDetNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStandardBasisExtensionDetNeZeroStatement
import Theorems.Thm_GlobalTheory_extend_linearIndependent_rows_by_standard_basis


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
theorem _root_.solution : ∀ {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K), LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧ (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by
  first | exact @GlobalTheory.extend_linearIndependent_rows_by_standard_basis | exact GlobalTheory.extend_linearIndependent_rows_by_standard_basis | (intros; apply GlobalTheory.extend_linearIndependent_rows_by_standard_basis <;> assumption)
end _root_.GlobalTheory.T
