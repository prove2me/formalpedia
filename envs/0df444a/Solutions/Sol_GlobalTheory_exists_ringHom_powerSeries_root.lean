-- Prove2me | solution 1 for GlobalTheory.exists_ringHom_powerSeries_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:55.767021+00:00
-- url     : https://prove2.me/submissions/e7815afe-6cbf-4318-9a4c-0a51e7ce375a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRoot
import Theorems.Thm_GlobalTheory_SeriesRoot_extendHom_expand
import Theorems.Thm_GlobalTheory_SeriesRoot_extendHom_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k →
      t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K,
        (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧
          ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  intro O K _ _ φ k t hk ht
  refine ⟨SeriesRoot.extendHom φ hk.ne' ht, fun a => ?_, SeriesRoot.extendHom_X φ hk.ne' ht,
    fun f => ?_⟩
  · rw [← SeriesRoot.extendHom_expand φ hk.ne' ht (PowerSeries.C a), expand_C]
  · change ∑ l ∈ Finset.range k, t ^ l * φ (SeriesRoot.residuePart k l f) ∈ _
    refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ (Subring.pow_mem _ ?_ l) ?_
    · exact Subring.subset_closure (Or.inr rfl)
    · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
end GlobalTheory
