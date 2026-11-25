-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.tateMatch_onQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:43.556841+00:00
-- url     : https://prove2.me/submissions/66940a14-97d7-4efb-937c-15eb7fe1ff47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Theorems.Thm_GlobalTheory_Ex_TateInh_isoRefl_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh
namespace GlobalTheory.Ex.TateInh
theorem _root_.solution {C : Type} [NormedField C] (q : Cˣ) (n : ℕ) (hn : Odd n) : (tateMatch q n hn).OnQ (isoRefl _) :=
  fun _ _ _ a b => ⟨0, by rw [smul_zero, add_zero]; exact a, by rw [NumD.io_zero, mul_one]; exact (isoRefl_rel _ _ _).1 b⟩
end GlobalTheory.Ex.TateInh
