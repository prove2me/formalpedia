-- Prove2me | solution 1 for GlobalTheory.FrameNet.card_Icc_floor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:28.048655+00:00
-- url     : https://prove2.me/submissions/bb2fdbe8-0856-4321-87a6-d82ba2ae2214

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
namespace GlobalTheory.FrameNet
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) : ((Finset.Icc (0 : ℤ) ⌊t⌋).card : ℝ) ≤ t + 1 := by
  rw [Int.card_Icc, sub_zero]
  have h0 : 0 ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht
  have e : (((⌊t⌋ + 1).toNat : ℕ) : ℝ) = ((⌊t⌋ + 1 : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [e]
  push_cast
  linarith [Int.floor_le t]
end GlobalTheory.FrameNet
