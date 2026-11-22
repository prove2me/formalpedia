-- Prove2me | solution 1 for MarkushevichBasis.isMarkushevichBasis_dual_of_hilbert
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:53:49.020375+00:00
-- url     : https://prove2.me/submissions/3bba37cb-9e06-4778-91db-db264d2db571

import Mathlib
import Definitions.Def_MarkushevichBasis_Basic

open MarkushevichBasis Set

set_option autoImplicit false

theorem solution {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {ι : Type*} (x : ι → H) (f : ι → StrongDual 𝕜 H) (hxf : IsMarkushevichBasis x f) :
    IsMarkushevichBasis f (fun i => NormedSpace.inclusionInDoubleDual 𝕜 H (x i)) := by
  let e := InnerProductSpace.toDual 𝕜 H
  let g : ι → H := fun i => e.symm (f i)
  let S := Submodule.span 𝕜 (range g)
  have he : ∀ i, e (g i) = f i := fun i => e.apply_symm_apply (f i)
  have hS : Dense (S : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
    apply eq_bot_iff.mpr
    intro v hv
    rw [Submodule.mem_bot]
    apply hxf.total
    intro i
    have hInner := (S.mem_orthogonal v).mp hv (g i) (Submodule.subset_span (mem_range_self i))
    rwa [← InnerProductSpace.toDual_apply_apply, show InnerProductSpace.toDual 𝕜 H (g i) = f i from he i]
      at hInner
  have hImage : e '' (S : Set H) = (Submodule.span 𝕜 (range f) : Set (StrongDual 𝕜 H)) := by
    have hRange : (e : H → StrongDual 𝕜 H) '' range g = range f := by
      rw [← range_comp]
      exact congrArg range (funext he)
    change (S.map e.toLinearEquiv.toLinearMap : Set (StrongDual 𝕜 H)) = _
    unfold S
    rw [Submodule.map_span]
    exact congrArg (fun A => (Submodule.span 𝕜 A : Set (StrongDual 𝕜 H))) hRange
  refine ⟨hxf.apply_self, fun i j hij => hxf.apply_of_ne j i (Ne.symm hij), ?_, ?_⟩
  · rw [← hImage]
    intro ψ
    obtain ⟨v, rfl⟩ := e.surjective ψ
    exact image_closure_subset_closure_image e.continuous (mem_image_of_mem _ (hS v))
  · intro ψ hψ
    have hKer : Submodule.span 𝕜 (range x) ≤ ψ.ker := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hψ i
    ext v
    exact closure_minimal hKer ψ.isClosed_ker (hxf.dense_span v)
