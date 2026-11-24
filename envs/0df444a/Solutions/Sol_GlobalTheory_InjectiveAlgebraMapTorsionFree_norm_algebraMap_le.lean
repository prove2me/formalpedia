-- Prove2me | solution 1 for GlobalTheory.InjectiveAlgebraMapTorsionFree.norm_algebraMap_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:59.469715+00:00
-- url     : https://prove2.me/submissions/4e176c0e-f7d0-4607-a57d-fe8a92b16d57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InjectiveAlgebraMapTorsionFree
variable (p : ℕ) [Fact (Nat.Prime p)]
namespace GlobalTheory.InjectiveAlgebraMapTorsionFree
theorem _root_.solution (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), PadicAlgCl.norm_extends]
  simpa using PadicInt.norm_le_one a
end GlobalTheory.InjectiveAlgebraMapTorsionFree
