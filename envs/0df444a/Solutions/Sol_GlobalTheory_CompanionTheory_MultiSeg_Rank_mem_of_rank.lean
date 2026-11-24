-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.mem_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:10:49.412612+00:00
-- url     : https://prove2.me/submissions/7a18d9cd-1d96-47f8-b0a6-943b7ec12927

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_dec_eq_word
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_con_word_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_aseg_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_con_self

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
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {a b : Multiset (ASeg T)} {Δ : ASeg T}
    (hΔ : Δ ∈ a) (hb : ∀ Γ ∈ b, Γ.len ≤ Δ.len)
    (h : rank s a Δ.start (Δ.len - 1) = rank s b Δ.start (Δ.len - 1)) : Δ ∈ b := by
  have h1 : 0 < rank s a Δ.start (Δ.len - 1) := by
    unfold rank
    rw [Multiset.countP_pos]
    exact ⟨Δ, hΔ, con_self hs hp Δ⟩
  rw [h] at h1
  unfold rank at h1
  rw [Multiset.countP_pos] at h1
  obtain ⟨Γ, hΓ, hc⟩ := h1
  rw [dec_eq_word, con_word_iff hs hp] at hc
  obtain ⟨i, hi, hst⟩ := hc
  have hl := hb Γ hΓ
  have hpos := Δ.len_pos
  have hi0 : i = 0 := by omega
  subst hi0
  have : Γ = Δ := aseg_eq hst (by omega)
  rw [← this]
  exact hΓ
end GlobalTheory.CompanionTheory.MultiSeg.Rank
