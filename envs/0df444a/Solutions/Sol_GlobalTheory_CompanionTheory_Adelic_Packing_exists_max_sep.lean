-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.Packing.exists_max_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:17:24.096951+00:00
-- url     : https://prove2.me/submissions/8fbab705-48b2-4e6d-bcd2-95019f958c1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBound
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_Packing_Sep_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.Packing
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]
namespace GlobalTheory.CompanionTheory.Adelic.Packing
theorem _root_.solution (e : Λ →+ V) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ s : Finset Λ, Sep e r R s ∧ ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card := by
  let S : Set ℕ := {n | ∃ s : Finset Λ, Sep e r R s ∧ s.card = n}
  have hne : S.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hbd : BddAbove S := by
    refine ⟨⌊(3 * R / r) ^ Module.finrank ℝ V⌋₊, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact Nat.le_floor (Sep.card_le hr hrR hs)
  obtain ⟨s, hs, hc⟩ := Nat.sSup_mem hne hbd
  exact ⟨s, hs, fun t ht => hc ▸ le_csSup hbd ⟨t, ht, rfl⟩⟩
end GlobalTheory.CompanionTheory.Adelic.Packing
