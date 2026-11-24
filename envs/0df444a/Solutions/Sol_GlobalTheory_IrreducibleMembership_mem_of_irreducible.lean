-- Prove2me | solution 1 for GlobalTheory.IrreducibleMembership.mem_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:53:51.566978+00:00
-- url     : https://prove2.me/submissions/40864911-45f1-4a9c-aa38-a223fafb87a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemOfIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IrreducibleMembership
namespace GlobalTheory.IrreducibleMembership
theorem _root_.solution {K : Type u_1} {V : Type u_2} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf1 : f = 1 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf1]
    exact S.one_mem
  · have hso : IsSimpleOrder (Submodule S V) := by
      refine ⟨fun N => ?_⟩
      have hN := h (N.restrictScalars K) fun g hg v hv => by
        have hmem : (⟨g, hg⟩ : S) • v ∈ N := N.smul_mem _ hv
        exact hmem
      rcases hN with hN | hN
      · left
        exact (Submodule.restrictScalars_eq_bot_iff K S V).1 hN
      · right
        exact (Submodule.restrictScalars_eq_top_iff K S V).1 hN
    have hsimp : IsSimpleModule S V := ⟨⟩
    have hbij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K
    let F : Module.End (Module.End S V) V :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun g v => by
          obtain ⟨c, hc⟩ := hbij.2 g
          rw [← hc]
          simp }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
    have hfr : f = (r : Module.End K V) := by
      refine b.ext fun i => ?_
      have := hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
      exact this
    rw [hfr]
    exact r.2
end GlobalTheory.IrreducibleMembership
