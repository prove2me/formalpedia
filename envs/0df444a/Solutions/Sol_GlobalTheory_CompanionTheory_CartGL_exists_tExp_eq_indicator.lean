-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.exists_tExp_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:47.061855+00:00
-- url     : https://prove2.me/submissions/016409bb-3058-43df-bddb-afb89cf4aefb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntitonePowersInDominantMonoid
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartGL
theorem _root_.solution (b : Fin n → ℤ) (hb : Antitone b) :
    ∃ i : Fin (n + 2), tExp n i = fun j => if 0 < b j then 1 else 0 := by
  classical
  have hex : ∃ i : ℕ, i = n ∨ ∃ h : i < n, b ⟨i, h⟩ ≤ 0 := ⟨n, Or.inl rfl⟩
  have hle : Nat.find hex ≤ n := Nat.find_min' hex (Or.inl rfl)
  refine ⟨⟨Nat.find hex, by omega⟩, ?_⟩
  funext j
  have hne : Nat.find hex ≠ n + 1 := by omega
  simp only [tExp, hne, if_false]
  by_cases hj : (j : ℕ) < Nat.find hex
  · have hnot := Nat.find_min hex hj
    have hpos : 0 < b j := by
      by_contra hcon
      exact hnot (Or.inr ⟨j.2, not_lt.mp hcon⟩)
    rw [if_pos hj, if_pos hpos]
  · have hspec := Nat.find_spec hex
    have hnpos : ¬ 0 < b j := by
      rcases hspec with h | ⟨h, h'⟩
      · have := j.2
        omega
      · have hmono : b j ≤ b ⟨Nat.find hex, h⟩ := hb (by
          rw [Fin.le_def]
          exact not_lt.mp hj)
        omega
    rw [if_neg hj, if_neg hnpos]
end GlobalTheory.CompanionTheory.CartGL
