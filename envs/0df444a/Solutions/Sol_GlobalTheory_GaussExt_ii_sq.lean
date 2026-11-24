-- Prove2me | solution 1 for GlobalTheory.GaussExt.ii_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:21.741689+00:00
-- url     : https://prove2.me/submissions/30961312-43eb-4e3d-ad3d-98109bd70d0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open GlobalTheory GlobalTheory.GaussExt
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.GaussExt
theorem _root_.solution : ii F ^ 2 = -1 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : F[X])
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  rw [ii]; linear_combination h
end GlobalTheory.GaussExt
