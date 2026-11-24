-- Prove2me | solution 1 for GlobalTheory.EqualityOnPoints.eq_on_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:41:05.112016+00:00
-- url     : https://prove2.me/submissions/45414c94-0712-4a94-a6ae-dbd1b18db23a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits
open GlobalTheory GlobalTheory.EqualityOnPoints
namespace GlobalTheory.EqualityOnPoints
theorem _root_.solution {W X Y Z : Scheme.{0}} {a b : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : a ≫ s = b ≫ s) (i : W ⟶ X) [IsDominant i] (hi : i ≫ a = i ≫ b) (x : X) :
    (a x : Y) = b x := by

  set l := pullback.lift a b h with hl
  have hcl : IsClosed (l ⁻¹' Set.range (pullback.diagonal s)) :=
    (pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage l.continuous

  have he : i ≫ l = (i ≫ a) ≫ pullback.diagonal s := by
    apply pullback.hom_ext
    · rw [hl, Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [hl, Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, hi]
  have hsub : Set.range i ⊆ l ⁻¹' Set.range (pullback.diagonal s) := by
    rintro _ ⟨w, rfl⟩
    refine ⟨(i ≫ a) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply]

  have hall : l x ∈ Set.range (pullback.diagonal s) := by
    have hcl' := hcl.closure_subset_iff.2 hsub
    rw [i.denseRange.closure_range] at hcl'
    exact hcl' (Set.mem_univ x)
  obtain ⟨y, hy⟩ := hall
  have ha : a x = y := by
    have e : (pullback.diagonal s ≫ pullback.fst s s) y = (l ≫ pullback.fst s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_fst, hl, pullback.lift_fst] at e
    simpa using e.symm
  have hb : b x = y := by
    have e : (pullback.diagonal s ≫ pullback.snd s s) y = (l ≫ pullback.snd s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_snd, hl, pullback.lift_snd] at e
    simpa using e.symm
  rw [ha, hb]
end GlobalTheory.EqualityOnPoints
