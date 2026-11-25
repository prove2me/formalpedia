-- Prove2me | solution 1 for GlobalTheory.PDivGroup.hodgeTate_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:08.157805+00:00
-- url     : https://prove2.me/submissions/e0d285f6-12ae-4d53-b718-fe58b995f430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDivGroup_hodgeTate_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable {G H : PDivGroup p O}
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (φ : ℤ_[p] →+* O) (a : ℤ_[p]) (t : G.Tate) :
    hodgeTate G (a • t) = φ a • hodgeTate G t := by
  rw [hodgeTate_apply, map_smul, dlog_smul φ, hodgeTate_apply]
end GlobalTheory.PDivGroup
