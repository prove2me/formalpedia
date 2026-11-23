-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.iter_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:23.126824+00:00
-- url     : https://prove2.me/submissions/7ed22edd-ddd6-425d-9a17-6c144892cdb7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt

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
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {t : T} {a b : ℕ}
    (h : s^[a] t = s^[b] t) : a = b := by
  have key : ∀ a b : ℕ, a ≤ b → s^[a] t = s^[b] t → a = b := by
    intro a b hab h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [Function.iterate_add_apply] at h
    have h' : s^[k] t = t := ((hs.iterate a) h).symm
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · exact absurd h' (hp t k hk)
  rcases le_total a b with hab | hab
  · exact key a b hab h
  · exact (key b a hab h.symm).symm
end GlobalTheory.CompanionTheory.MultiSeg.Rank
