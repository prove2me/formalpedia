-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.sum_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:35.176049+00:00
-- url     : https://prove2.me/submissions/3f594a36-5837-42f2-b439-ca4b9fdb41fd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_iter_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_sum_sub_wd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
open Classical
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MultiSeg GlobalTheory.CompanionTheory.MultiSeg.Rank
variable {T : Type u}
namespace GlobalTheory.CompanionTheory.MultiSeg.Rank
theorem _root_.solution {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) (Δ : ASeg T) :
    ∑ q ∈ pairs s Δ, wd q.2 = Δ.len ^ 2 := by
  unfold pairs
  rw [Finset.sum_image]
  · rw [Finset.sum_sigma]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    exact sum_sub_wd Δ.len
  · rintro ⟨d, i⟩ _ ⟨d', i'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have := iter_inj hs hp h1
    subst h2
    subst this
    rfl
end GlobalTheory.CompanionTheory.MultiSeg.Rank
