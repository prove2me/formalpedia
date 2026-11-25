-- Prove2me | solution 1 for GlobalTheory.continuous_mat_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:03.307971+00:00
-- url     : https://prove2.me/submissions/8938df27-d37f-4872-a618-4c160f8db7db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCandidateBorelMoveOpenFramesBaire

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
noncomputable section
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (g : GL (Fin r) E) (τ : Ψ) :
    Continuous fun z : Frame Ψ r => mat (lact g z) τ := by
  have h : Continuous fun z : Frame Ψ r => mat z τ := continuous_apply τ
  exact continuous_const.matrix_mul h
end GlobalTheory
