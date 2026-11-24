-- Prove2me | solution 1 for GlobalTheory.affine_inter_finite_basicOpen_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:10.850745+00:00
-- url     : https://prove2.me/submissions/82848fc7-1355-4533-a912-26859f1f3cb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry TopologicalSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V →
      ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧
        ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by
  intro X hX W V hW hV
  classical
  have key : ∀ x : ((W ⊓ V : X.Opens) : Set X), ∃ (f : Γ(X, W)) (g : Γ(X, V)),
      X.basicOpen f = X.basicOpen g ∧ (x : X) ∈ X.basicOpen f :=
    fun x => exists_basicOpen_le_affine_inter hW hV x.1 x.2
  choose f g hfg hx using key
  have hc : IsCompact ((W ⊓ V : X.Opens) : Set X) := NoetherianSpace.isCompact _
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hx _⟩)
  refine ⟨t.image f, ?_, ?_⟩
  · intro h hh
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hh
    exact ⟨g x, hfg x⟩
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact Set.mem_iUnion₂.2 ⟨f x, Finset.mem_image_of_mem f hxt, hyx⟩
end GlobalTheory
