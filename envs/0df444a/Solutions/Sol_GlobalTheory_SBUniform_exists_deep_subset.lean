-- Prove2me | solution 1 for GlobalTheory.SBUniform.exists_deep_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:39.179335+00:00
-- url     : https://prove2.me/submissions/fa2d29b3-7ee6-44fb-b897-7eec32a8da12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Theorems.Thm_GlobalTheory_SBUniform_eventually_deep_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open Filter Topology
open GlobalTheory GlobalTheory.SBUniform
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SBUniform
theorem _root_.solution {n : Type} [Fintype n] {s : Set (Matrix n n k)} (hs : s ∈ 𝓝 (0 : Matrix n n k)) :
    ∃ M : ℕ, ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → y ∈ s := by
  have hs' : s ∈ 𝓝 (0 : n → n → k) := hs
  rw [nhds_pi] at hs'
  obtain ⟨I, -, t, ht, hts⟩ := Filter.mem_pi.1 hs'

  have ht' : ∀ i, ∃ J : Set n, J.Finite ∧ ∃ u : n → Set k, (∀ j, u j ∈ 𝓝 (0 : k)) ∧ J.pi u ⊆ t i := by
    intro i
    have hi : t i ∈ 𝓝 (0 : n → k) := ht i
    rw [nhds_pi] at hi
    exact Filter.mem_pi.1 hi
  choose J _ u hu hJu using ht'
  have hev : ∀ᶠ M : ℕ in atTop, ∀ i j, ∀ x : k, Deep (M : ℤ) x → x ∈ u i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact eventually_deep_subset (hu i j)
  obtain ⟨M, hM⟩ := hev.exists
  exact ⟨M, fun y hy => hts (Set.mem_pi.2 fun i _ => hJu i (Set.mem_pi.2 fun j _ => hM i j _ (hy i j)))⟩
end GlobalTheory.SBUniform
