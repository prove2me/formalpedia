-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.Packing.Sep.exists_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:17:23.293104+00:00
-- url     : https://prove2.me/submissions/8c38321d-b88c-4566-8bb3-066689cea583

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBound

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
namespace Sep
theorem _root_.solution {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) {s : Finset Λ}
    (hs : Sep e r R s) (hmax : ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card)
    {l : Λ} (hl : ‖e l‖ ≤ R) : ∃ t ∈ s, ‖e (l - t)‖ ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  have hns : l ∉ s := fun h => by
    have := hcon l h
    simp only [sub_self, map_zero, norm_zero] at this
    linarith
  have hins : Sep e r R (insert l s) := by
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hl
      · exact hs.1 m hm
    · rw [Finset.coe_insert]
      refine Set.pairwise_insert.2 ⟨hs.2, ?_⟩
      intro b hb _
      have h := hcon b hb
      rw [map_sub] at h
      exact ⟨h.le, by rw [norm_sub_rev]; exact h.le⟩
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem hns] at this
  omega
end Sep
end GlobalTheory.CompanionTheory.Adelic.Packing
