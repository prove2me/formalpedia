-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.tateMatch_onG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:38.784114+00:00
-- url     : https://prove2.me/submissions/81657fc0-726d-445f-9cc5-5c7ecd01d559

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
theorem _root_.solution {C : Type} [NormedField C] (q : Cˣ) (n : ℕ) (hn : Odd n) : (tateMatch q n hn).OnG (isoRefl _) := by
  rintro j p p' ⟨z, h1, h2⟩ a b
  rw [a, b, toAdd_one, zero_add] at h1
  have key : ∀ w : ℤ, 0 = (n ^ j) • w → w = 0 := fun w hw =>
    (smul_eq_zero_iff_right (pow_ne_zero _ hn.pos.ne')).1 hw.symm
  have hz : z = 0 := key z h1
  rw [hz, NumD.io_zero, mul_one] at h2
  exact (isoRefl_rel _ _ _).2 h2
end GlobalTheory.Ex.TateInh
