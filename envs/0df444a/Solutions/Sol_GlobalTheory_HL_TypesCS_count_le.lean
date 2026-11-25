-- Prove2me | solution 1 for GlobalTheory.HL.TypesCS.count_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:21.302788+00:00
-- url     : https://prove2.me/submissions/a6fa9a8c-05fb-4739-a362-28d805a17102

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexEqCardMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmpSqLeCardMulSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmpSqLeOfHermitianTermTypesCauchySchwarz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TypesCS
namespace GlobalTheory.HL.TypesCS
theorem _root_.solution (r a : ℕ) (H : ℝ) (ha : 1 ≤ a) (hH : (2 : ℝ) ^ a ≤ H) :
    ((a + a * (r * a) : ℕ) : ℝ) ≤ H ^ (r + 2) := by
  have hnat : a + a * (r * a) ≤ 2 ^ (a * (r + 2)) := by
    have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2 : r * a < 2 ^ (r * a) := Nat.lt_two_pow_self
    calc a + a * (r * a) = a * (1 + r * a) := by ring
      _ ≤ 2 ^ a * 2 ^ (r * a) := Nat.mul_le_mul h1.le (by omega)
      _ = 2 ^ (a + r * a) := (pow_add 2 a (r * a)).symm
      _ ≤ 2 ^ (a * (r + 2)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc ((a + a * (r * a) : ℕ) : ℝ) ≤ ((2 ^ (a * (r + 2)) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((2 : ℝ) ^ a) ^ (r + 2) := by push_cast; rw [pow_mul]
    _ ≤ H ^ (r + 2) := by gcongr
end GlobalTheory.HL.TypesCS
