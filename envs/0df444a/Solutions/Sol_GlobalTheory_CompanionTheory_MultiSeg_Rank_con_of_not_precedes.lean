-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.con_of_not_precedes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:37.884088+00:00
-- url     : https://prove2.me/submissions/f0aa6732-82ee-4437-80fc-a5bae78de2c6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_iter_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_mem_word
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_dec_eq_word
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_con_word_iff

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
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {Γ Θ : ASeg T} {u : T} {j d : ℕ}
    (hΘ : Θ.start = s^[j + 1] u) (hu : u ∉ Θ.dec s) (hv : s^[d] u ∈ Θ.dec s)
    (hc : Con s u j (Γ.dec s)) (hn : ¬ APrecedes s Γ Θ) : Con s u d (Γ.dec s) := by
  have memC : ∀ (Δ : ASeg T) (x : T), x ∈ Δ.carrier s ↔ ∃ k < Δ.len, s^[k] Δ.start = x :=
    fun Δ x => Iff.rfl
  simp only [dec_eq_word] at hu hv hc ⊢
  rw [con_word_iff hs hp] at hc
  rw [con_word_iff hs hp]
  obtain ⟨i, hij, hiu⟩ := hc
  by_contra hcon
  apply hn
  have hd : Γ.len ≤ i + d := by
    by_contra h
    exact hcon ⟨i, by omega, hiu⟩
  have hΘs : Θ.start = s^[j + 1 + i] Γ.start := by
    rw [hΘ, ← hiu]
    exact (Function.iterate_add_apply s (j + 1) i Γ.start).symm
  show ((∃ Γ' : ASeg T, Γ'.carrier s = Γ.carrier s ∪ Θ.carrier s) ∧ ¬ Γ.carrier s ⊆ Θ.carrier s ∧
    ¬ Θ.carrier s ⊆ Γ.carrier s) ∧ ∃ j' : ℕ, 0 < j' ∧ Θ.start = s^[j'] Γ.start
  refine ⟨⟨⟨⟨Γ.start, max Γ.len (j + 1 + i + Θ.len), lt_max_of_lt_left Γ.len_pos⟩, ?_⟩, ?_, ?_⟩,
    j + 1 + i, by omega, hΘs⟩
  · ext x
    rw [Set.mem_union, memC, memC, memC]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases lt_max_iff.1 hk with hk | hk
      · exact Or.inl ⟨k, hk, rfl⟩
      · by_cases hkl : k < Γ.len
        · exact Or.inl ⟨k, hkl, rfl⟩
        · right
          refine ⟨k - (j + 1 + i), by omega, ?_⟩
          exact (by
            rw [hΘs, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : j + 1 + i ≤ k)] :
            s^[k - (j + 1 + i)] Θ.start = s^[k] Γ.start)
    · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
      · exact ⟨k, lt_max_iff.2 (Or.inl hk), rfl⟩
      · refine ⟨k + (j + 1 + i), lt_max_iff.2 (Or.inr (by omega)), ?_⟩
        exact (by rw [hΘs]; exact Function.iterate_add_apply s k (j + 1 + i) Γ.start :
          s^[k + (j + 1 + i)] Γ.start = s^[k] Θ.start)
  · intro hsub
    exact hu (mem_word.2 ((memC Θ u).1 (hsub ((memC Γ u).2 ⟨i, by omega, hiu⟩))))
  · intro hsub
    obtain ⟨k, hk, hk'⟩ := (memC Γ _).1 (hsub ((memC Θ _).2 (mem_word.1 hv)))
    rw [← hiu, ← Function.iterate_add_apply] at hk'
    have := iter_inj hs hp hk'
    omega
end GlobalTheory.CompanionTheory.MultiSeg.Rank
