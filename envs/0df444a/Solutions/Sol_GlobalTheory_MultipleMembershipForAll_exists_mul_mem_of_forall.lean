-- Prove2me | solution 1 for GlobalTheory.MultipleMembershipForAll.exists_mul_mem_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:00:43.730239+00:00
-- url     : https://prove2.me/submissions/993dc4e8-7acd-4763-9cf0-5204cae5a133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulMemOfForall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultipleMembershipForAll
open IsLocalRing
namespace GlobalTheory.MultipleMembershipForAll
theorem _root_.solution {S : Type} [CommRing S] (Q I : Ideal S) [hQp : Q.IsPrime]
    (hQ : Q.FG) (h : ∀ x ∈ Q, ∃ g ∉ Q, g * x ∈ I) : ∃ g ∉ Q, ∀ x ∈ Q, g * x ∈ I := by
  classical
  obtain ⟨s, hs⟩ := hQ

  suffices H : ∀ s' : Finset S, (s' : Set S) ⊆ Q →
      ∃ g ∉ Q, ∀ x ∈ Ideal.span (s' : Set S), g * x ∈ I by
    obtain ⟨g, hg, hgI⟩ := H s (by rw [← hs]; exact Submodule.subset_span)
    exact ⟨g, hg, fun x hx => hgI x (by rw [hs]; exact hx)⟩
  intro s'
  induction s' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨1, fun h1 => hQp.ne_top ((Ideal.eq_top_iff_one Q).mpr h1), fun x hx => ?_⟩
    rw [Finset.coe_empty, Ideal.span_empty, Ideal.mem_bot] at hx
    simp [hx]
  | insert a s' ha ih =>
    intro hsub
    rw [Finset.coe_insert] at hsub
    obtain ⟨g, hg, hgI⟩ := ih ((Set.subset_insert _ _).trans hsub)
    obtain ⟨ga, hga, hgaI⟩ := h a (hsub (Set.mem_insert _ _))
    refine ⟨ga * g, fun hm => (hQp.mem_or_mem hm).elim hga hg, fun x hx => ?_⟩
    rw [Finset.coe_insert, Ideal.span_insert, Submodule.mem_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e1 : ga * g * (r * a + z) = (r * g) * (ga * a) + ga * (g * z) := by ring
    rw [e1]
    exact I.add_mem (I.mul_mem_left _ hgaI) (I.mul_mem_left _ (hgI z hz))
end GlobalTheory.MultipleMembershipForAll
