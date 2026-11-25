-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.tateMatch_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:58.469372+00:00
-- url     : https://prove2.me/submissions/c752635a-0108-41e0-bdca-0c252e49d619

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_equivalence


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
theorem _root_.solution {C : Type} [NormedField C] (q : Cˣ) (n : ℕ) (hn : Odd n) : (tateMatch q n hn).A := by
  refine ⟨norm_one, fun j p p' h => ⟨?_, ?_⟩⟩
  · obtain ⟨z, h1, -⟩ := h
    exact ⟨fun ⟨w, hw⟩ => ⟨w + z, by rw [h1, hw, smul_add]⟩, fun ⟨w, hw⟩ => ⟨w - z, by rw [smul_sub, ← hw, h1, add_sub_cancel_right]⟩⟩
  · have E := (tate q).qEq_equivalence (n ^ j)
    exact ⟨fun ⟨r, a, b⟩ => ⟨r, E.trans (E.symm h) a, b⟩, fun ⟨r, a, b⟩ => ⟨r, E.trans h a, b⟩⟩
end GlobalTheory.Ex.TateInh
