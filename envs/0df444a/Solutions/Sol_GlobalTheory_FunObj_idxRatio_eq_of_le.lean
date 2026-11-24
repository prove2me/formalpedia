-- Prove2me | solution 1 for GlobalTheory.FunObj.idxRatio_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:52:50.07947+00:00
-- url     : https://prove2.me/submissions/82a4e45a-9db2-449e-bbf1-09fd27e8fd5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open Matrix
variable {G : Type*} [Group G]
namespace GlobalTheory.FunObj
theorem _root_.solution {A B D : Subgroup G} (hD : D ≤ A ⊓ B) (h0 : D.relIndex (A ⊓ B) ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / D.relIndex B := by
  have h1 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) A hD inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) B hD inf_le_right
  have e1 : (A ⊓ B).relIndex A = B.relIndex A := by rw [inf_comm]; exact Subgroup.inf_relIndex_right B A
  have e2 : (A ⊓ B).relIndex B = A.relIndex B := Subgroup.inf_relIndex_right A B
  rw [idxRatio, ← h1, ← h2, e1, e2]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast h0)]
end GlobalTheory.FunObj
