-- Prove2me | solution 1 for KrullIntersectionUnits.KrullIntersectionLemmas.exists_unit_kills_of_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:47.605802+00:00
-- url     : https://prove2.me/submissions/ccd8e206-eec9-4bc6-9930-1f9353e3ed29

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KrullIntersectionUnits KrullIntersectionUnits.KrullIntersectionLemmas
namespace KrullIntersectionUnits.KrullIntersectionLemmas
theorem _root_.solution {A : Type} [CommRing A] (J : Ideal A) (S : Finset A) :
    (∀ x ∈ S, ∃ r ∈ J, r * x = x) → ∃ s : A, s - 1 ∈ J ∧ ∀ x ∈ S, s * x = 0 := by
  classical
  refine Finset.induction_on S ?_ ?_
  · intro _
    exact ⟨1, by simp, by simp⟩
  · intro x S _ ih h
    obtain ⟨s, hs1, hs2⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    obtain ⟨r, hrJ, hrx⟩ := h x (Finset.mem_insert_self x S)
    refine ⟨s * (1 - r), ?_, ?_⟩
    · have e : s * (1 - r) - 1 = (s - 1) - s * r := by ring
      rw [e]
      exact J.sub_mem hs1 (J.mul_mem_left s hrJ)
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · have e : s * (1 - r) * y = s * (y - r * y) := by ring
        rw [e, hrx, sub_self, mul_zero]
      · have e : s * (1 - r) * y = (1 - r) * (s * y) := by ring
        rw [e, hs2 y hy, mul_zero]
end KrullIntersectionUnits.KrullIntersectionLemmas
