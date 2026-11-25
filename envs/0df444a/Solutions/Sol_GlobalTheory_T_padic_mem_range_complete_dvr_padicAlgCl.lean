-- Prove2me | solution 1 for GlobalTheory.T.padic_mem_range_complete_dvr_padicAlgCl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:22.345223+00:00
-- url     : https://prove2.me/submissions/1cbcbb21-4abf-4264-98fd-46a2c24bdd85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgClStatement
import Theorems.Thm_GlobalTheory_PadicUnitBall_padic_mem_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by
  first | exact @GlobalTheory.PadicUnitBall.padic_mem_range | exact GlobalTheory.PadicUnitBall.padic_mem_range | (intros; apply GlobalTheory.PadicUnitBall.padic_mem_range <;> assumption)
end _root_.GlobalTheory.T
