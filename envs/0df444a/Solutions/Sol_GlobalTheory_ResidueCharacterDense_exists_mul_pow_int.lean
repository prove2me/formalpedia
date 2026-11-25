-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.exists_mul_pow_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:27:40.536805+00:00
-- url     : https://prove2.me/submissions/8f9d78cb-5b2f-4129-9ce8-bd160aed6938

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
open Formalism.MainNotions.S.Loc
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution (a : ℚ) (l n : ℕ) (h : a.den = l ^ n) (N : ℕ) (hN : n ≤ N) :
    ∃ m : ℤ, a * (l : ℚ) ^ N = m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨a.num * l ^ j, ?_⟩
  have : a * (l : ℚ) ^ n = a.num := by
    rw [← Rat.mul_den_eq_num, h]; push_cast; rfl
  rw [pow_add, ← mul_assoc, this]
  push_cast
  rfl
end GlobalTheory.ResidueCharacterDense
