-- Prove2me | solution 1 for GlobalTheory.HostModel.zeta_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:22.256627+00:00
-- url     : https://prove2.me/submissions/0d1b8d96-e1f2-4698-8f94-c68be53ff827

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HostModel
theorem _root_.solution {a n : ℕ} (hn : 0 < n) (h : a ∣ n) : zeta n ^ (n / a) = zeta a := by
  obtain ⟨k, rfl⟩ := h
  have ha : 0 < a := Nat.pos_of_mul_pos_right hn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left k ha, zeta_mul_pow ha hk]
end GlobalTheory.HostModel
