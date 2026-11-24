-- Prove2me | solution 1 for GlobalTheory.LocalRingBasicFacts.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:11.105946+00:00
-- url     : https://prove2.me/submissions/698bdd1d-5bbe-48ef-8665-270d1dcfe173

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocalRingBasicFacts
namespace GlobalTheory.LocalRingBasicFacts
theorem _root_.solution : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ}, Ideal.span (Set.range MvPowerSeries.X) ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  intro O _ _ a
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have := h.map (MvPowerSeries.constantCoeff (R := O) (σ := Fin a))
  simp at this
end GlobalTheory.LocalRingBasicFacts
