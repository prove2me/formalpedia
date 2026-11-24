-- Prove2me | solution 1 for GlobalTheory.PBasis.exists_pBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:06:52.041267+00:00
-- url     : https://prove2.me/submissions/e18539fb-6220-4a1e-b82a-2555a52fad53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
import Theorems.Thm_GlobalTheory_PBasis_map_graphRing
import Theorems.Thm_GlobalTheory_PBasis_indep_empty
import Theorems.Thm_GlobalTheory_PBasis_indep_sUnion
import Theorems.Thm_GlobalTheory_PBasis_indep_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.PBasis
variable {k : Type} [Field k]
namespace GlobalTheory.PBasis
theorem _root_.solution : ∀ (k : Type) [Field k] (p : ℕ), p.Prime → (p : k) = 0 → ∃ B : Set k, Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤ ∧ ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) → ∃ σ : k →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b := by
  intro k _ p hp h0
  obtain ⟨B, -, hB⟩ := zorn_subset_nonempty {B : Set k | Indep p B}
    (fun c hc hch hne => ⟨⋃₀ c, indep_sUnion p c hch hne hc, fun s hs => Set.subset_sUnion_of_mem hs⟩)
    ∅ (indep_empty hp h0)
  have htop : Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    by_contra ha
    have := hB.le_of_ge (indep_insert hp h0 hB.prop ha) (Set.subset_insert a B)
    exact ha (Subring.subset_closure (Or.inr (this (Set.mem_insert a B))))
  refine ⟨B, htop, fun Q _ f g hg => ?_⟩
  have hI := hB.prop Q f g hg
  set S := graphRing p f g B with hS
  let φ : S →+* k := (RingHom.fst k Q).comp S.subtype
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro s hs
      exact Subtype.ext (Prod.ext hs (hI s s.2 hs))
    · intro x
      have : x ∈ S.map (RingHom.fst k Q) := by
        rw [hS, map_graphRing, htop]; trivial
      obtain ⟨s, hs, rfl⟩ := this
      exact ⟨⟨s, hs⟩, rfl⟩
  let e := RingEquiv.ofBijective φ hφ
  have key : ∀ s : S, ((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom (s : k × Q).1 = (s : k × Q).2 := by
    intro s
    have : e.symm (s : k × Q).1 = s := e.symm_apply_apply s
    change ((e.symm (s : k × Q).1 : S) : k × Q).2 = _
    rw [this]
  refine ⟨((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom, fun x => ?_, fun b hb => ?_⟩
  · exact key ⟨(x ^ p, f x), Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩
  · exact key ⟨(b, g b), Subring.subset_closure (Or.inr ⟨b, hb, rfl⟩)⟩
end GlobalTheory.PBasis
