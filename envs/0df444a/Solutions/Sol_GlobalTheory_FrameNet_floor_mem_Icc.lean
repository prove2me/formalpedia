-- Prove2me | solution 1 for GlobalTheory.FrameNet.floor_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:29.810019+00:00
-- url     : https://prove2.me/submissions/f0ead107-de3c-4e90-8f37-6842a5ef89da

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
theorem _root_.solution {s δ a : ℝ} (hδ : 0 < δ) (h : |a| ≤ s) :
    ⌊(a + s) / δ⌋ ∈ Finset.Icc (0 : ℤ) ⌊2 * s / δ⌋ := by
  have ha := abs_le.mp h
  rw [Finset.mem_Icc]
  constructor
  · exact Int.floor_nonneg.mpr (div_nonneg (by linarith) hδ.le)
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hδ.le)
end GlobalTheory.FrameNet
