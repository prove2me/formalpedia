-- Prove2me | solution 1 for GlobalTheory.HL.TotalWeight.natCast_pow_le_pow_of_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:57.516047+00:00
-- url     : https://prove2.me/submissions/8883de53-77a9-48d8-ab71-5fb355c57173

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RmulMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumClsLeEncard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassesTotalWeightLe
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TotalWeight
namespace GlobalTheory.HL.TotalWeight
theorem _root_.solution (q m a e e' : ℕ) (he : e ≤ e') (h1 : (1 : ℝ) ≤ (q : ℝ) ^ (m + a)) :
    (q : ℝ) ^ (e * m) ≤ ((q : ℝ) ^ (m + a)) ^ e' := by
  have h2 : (q : ℝ) ^ m ≤ (q : ℝ) ^ (m + a) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simpa using h1
      · simp [hm.ne']
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) (Nat.le_add_right _ _)
  calc (q : ℝ) ^ (e * m) = ((q : ℝ) ^ m) ^ e := by rw [mul_comm, pow_mul]
    _ ≤ ((q : ℝ) ^ (m + a)) ^ e := pow_le_pow_left₀ (by positivity) h2 e
    _ ≤ _ := pow_le_pow_right₀ h1 he
end GlobalTheory.HL.TotalWeight
