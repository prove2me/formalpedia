-- Prove2me | solution 1 for GlobalTheory.GenEigenFinOrbit.exists_common_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:27:46.089227+00:00
-- url     : https://prove2.me/submissions/4d9ef385-d920-4efc-93bd-3124dad79485

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_map_prod_le
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_map_prod_eq_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.GenEigenFinOrbit
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (G : Set (End ℂ V)) (N : Submodule ℂ V) (K : ℕ)
  (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
  (hst : ∀ g ∈ G, N.map g ≤ N) (hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ K) n = 0)
include hcomm hst hnil
namespace GlobalTheory.GenEigenFinOrbit
theorem _root_.solution [FiniteDimensional ℂ N] (hN : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 0 ∧ ∀ g ∈ G, g n = 0 := by
  classical
  let Pr : ℕ → Prop := fun l => ∃ gs : List (End ℂ V), (∀ g ∈ gs, g ∈ G) ∧ gs.length = l ∧
    N.map gs.prod ≠ ⊥
  have hex : ∃ l, ¬ Pr l := ⟨finrank ℂ N, fun ⟨gs, hgs, hl, hne⟩ =>
    hne (map_prod_eq_bot G N K hcomm hst hnil gs hgs hl.ge)⟩
  have h0 : Pr 0 := ⟨[], by simp, rfl, by simpa [Module.End.one_eq_id] using hN⟩
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exact absurd (h ▸ Nat.find_spec hex) (not_not.2 h0)
    · exact h
  obtain ⟨gs, hgs, hl, hne⟩ : Pr (Nat.find hex - 1) :=
    not_not.1 (Nat.find_min hex (by omega))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨gs.prod n, map_prod_le G N hst gs hgs ⟨n, hn, rfl⟩, hx0, fun g hg => ?_⟩
  by_contra hne'
  apply Nat.find_spec hex
  refine ⟨g :: gs, ?_, by simp [hl]; omega, ?_⟩
  · intro x hx; simp at hx; rcases hx with rfl | hx; exacts [hg, hgs x hx]
  · intro hbot
    apply hne'
    have : (g :: gs).prod n ∈ N.map (g :: gs).prod := ⟨n, hn, rfl⟩
    rw [hbot] at this
    simpa [Module.End.mul_apply] using this
end GlobalTheory.GenEigenFinOrbit
