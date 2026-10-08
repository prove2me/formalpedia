-- Prove2me | solution 1 for MazurTransfer.integral_of_two_chart_gluing
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T20:16:30.553223+00:00
-- url     : https://prove2.me/submissions/bf5a00f3-5501-432e-b9f9-e8e3b511dc41

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: integral two-chart gluing, with explicit chart-integrality
and nonempty-overlap assumptions. Named downstream consumer:
MazurTorsion.XOneThirteenProjectiveCurve.curveScheme_isIntegral; its hypotheses
are independently checked on the original order-thirteen model.
-/
import Mathlib

noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
namespace MazurTransfer

theorem irreducible_of_two_open_charts
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IrreducibleSpace A] [IrreducibleSpace B]
    (f : A → C) (g : B → C) (hf : Continuous f) (hg : Continuous g)
    (hfo : IsOpen (Set.range f))
    (hcover : ∀ c, c ∈ Set.range f ∨ c ∈ Set.range g)
    (hoverlap : ∃ a b, f a = g b) : IrreducibleSpace C := by
  obtain ⟨a, b, hab⟩ := hoverlap
  have hpre (U : Set C) (hU : IsOpen U) (hne : U.Nonempty) :
      (f ⁻¹' U).Nonempty := by
    obtain ⟨c, hc⟩ := hne
    rcases hcover c with ⟨a', rfl⟩ | ⟨b', rfl⟩
    · exact ⟨a', hc⟩
    · obtain ⟨z, hzU, hzF⟩ := nonempty_preirreducible_inter
        (hU.preimage hg) (hfo.preimage hg) ⟨b', hc⟩ ⟨b, a, hab⟩
      obtain ⟨a', ha'⟩ := hzF
      refine ⟨a', ?_⟩
      change f a' ∈ U
      rw [ha']
      exact hzU
  haveI : PreirreducibleSpace C := PreirreducibleSpace.of_forall_nonempty_inter
    (by
      intro U V hU hV hUn hVn
      obtain ⟨a', haU, haV⟩ := nonempty_preirreducible_inter
        (hU.preimage hf) (hV.preimage hf) (hpre U hU hUn) (hpre V hV hVn)
      exact ⟨f a', haU, haV⟩)
  exact { toNonempty := Nonempty.map f inferInstance }


theorem integral_of_two_chart_gluing
    (D : Scheme.GlueData) (i j : D.J) (hcover : ∀ k, k = i ∨ k = j)
    [IsIntegral (D.U i)] [IsIntegral (D.U j)]
    (hoverlap : Nonempty (D.V (i, j))) : IsIntegral D.glued := by
  have hr : ∀ k : D.openCover.I₀, IsReduced (D.openCover.X k) := by
    intro k
    change IsReduced (D.U k)
    rcases hcover k with h | h
    · rw [h]; infer_instance
    · rw [h]; infer_instance
  haveI := hr
  haveI : IsReduced D.glued := IsReduced.of_openCover D.glued D.openCover
  have hpoint : ∃ a b, D.ι i a = D.ι j b := by
    let z := Classical.choice hoverlap
    exact ⟨D.f i j z, (D.t i j ≫ D.f j i) z,
      (D.ι_eq_iff i j _ _).mpr ⟨z, rfl, rfl⟩⟩
  haveI : IrreducibleSpace D.glued := irreducible_of_two_open_charts
    (D.ι i) (D.ι j) (D.ι i).continuous (D.ι j).continuous
    (D.ι i).isOpenEmbedding.isOpen_range (by
      intro c
      obtain ⟨k, x, hx⟩ := D.ι_jointly_surjective c
      rcases hcover k with rfl | rfl
      · exact Or.inl ⟨x, hx⟩
      · exact Or.inr ⟨x, hx⟩) hpoint
  exact isIntegral_of_irreducibleSpace_of_isReduced D.glued

end MazurTransfer

theorem solution (D : _root_.AlgebraicGeometry.Scheme.GlueData)
    (i j : D.J) (hcover : ∀ k, k = i ∨ k = j)
    [_root_.AlgebraicGeometry.IsIntegral (D.U i)]
    [_root_.AlgebraicGeometry.IsIntegral (D.U j)]
    (hoverlap : Nonempty (D.V (i, j))) :
    _root_.AlgebraicGeometry.IsIntegral D.glued :=
  MazurTransfer.integral_of_two_chart_gluing D i j hcover hoverlap
