-- Prove2me | solution 1 for GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:40:08.45827+00:00
-- url     : https://prove2.me/submissions/4306629d-a625-41a4-bdf2-b311f28535a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumMulLeftTransversal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LeftTransversalSum
namespace GlobalTheory.LeftTransversalSum
theorem _root_.solution {G M : Type} [Group G] [AddCommMonoid M] (H N : Subgroup G)
    (S : Finset G) (hS : ∀ s ∈ S, s ∈ H) (huniq : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ N)
    (f : G → M) (hf : ∀ (g n : G), n ∈ N → f (g * n) = f g) :
    ∀ h ∈ H, ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  intro h hh
  have hex : ∀ s : G, ∃ t : G, s ∈ S → t ∈ S ∧ t⁻¹ * (h * s) ∈ N := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨t, ht, -⟩ := huniq _ (H.mul_mem hh (hS s hs))
      exact ⟨t, fun _ => ht⟩
    · exact ⟨s, fun h' => absurd h' hs⟩
  choose σ hσ using hex
  have uniq : ∀ x ∈ H, ∀ t ∈ S, ∀ t' ∈ S, t⁻¹ * x ∈ N → t'⁻¹ * x ∈ N → t = t' :=
    fun x hx t ht t' ht' h1 h2 => (huniq x hx).unique ⟨ht, h1⟩ ⟨ht', h2⟩
  refine Finset.sum_nbij σ (fun s hs => (hσ s hs).1) ?_ ?_ ?_
  · intro s hs s' hs' he
    have n1 := (hσ s hs).2
    have n2 := (hσ s' hs').2
    rw [← he] at n2
    have hss : s⁻¹ * s' ∈ N := by
      convert N.mul_mem (N.inv_mem n1) n2 using 1
      group
    exact uniq s' (hS s' hs') s hs s' hs' hss (by simp)
  · intro t ht
    obtain ⟨s, ⟨hs, hsN⟩, -⟩ := huniq (h⁻¹ * t) (H.mul_mem (H.inv_mem hh) (hS t ht))
    refine ⟨s, hs, ?_⟩
    refine uniq (h * s) (H.mul_mem hh (hS s hs)) _ (hσ s hs).1 t ht (hσ s hs).2 ?_
    convert N.inv_mem hsN using 1
    group
  · intro s hs
    have e := hf (σ s) ((σ s)⁻¹ * (h * s)) (hσ s hs).2
    rw [mul_inv_cancel_left] at e
    exact e
end GlobalTheory.LeftTransversalSum
