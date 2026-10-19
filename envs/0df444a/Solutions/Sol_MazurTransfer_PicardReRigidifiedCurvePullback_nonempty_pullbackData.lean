-- Prove2me | solution 1 for MazurTransfer.PicardReRigidifiedCurvePullback.nonempty_pullbackData
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T11:29:39.40716+00:00
-- url     : https://prove2.me/submissions/4630b719-4c94-49c8-a844-2dc1ea4b2135

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Original official Anthropic FLT re-rigidified pullback construction at
6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: actual pullback data for a curve morphism over the base.
Named downstream consumer: rational Picard diamond scheme endomorphism. -/
import Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer.PicardReRigidifiedCurvePullback
variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {D : RelativePic0Designation R c}
theorem solution (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (f : C ⟶ C) (hf : f ≫ c = c) : Nonempty (PullbackData h f hf) := by
  have hf' : f ≫ c = c ≫ 𝟙 _ := hf.trans (Category.comp_id c).symm
  obtain ⟨N, hclass, hmul, hone⟩ :=
    h.exists_hom_classifies_rigidify_pullback_map_of_comp_eq_comp (𝟙 _) (𝟙 _)
      (Category.id_comp _) (Category.id_comp _) f hf'
  let N' : SchemeHomOver D.toBase D.toBase := ⟨N.1, N.2.trans (Category.comp_id D.toBase)⟩
  refine ⟨⟨N', ?_, ?_, ?_⟩⟩
  · intro T t a
    have ht : t ≫ 𝟙 (Spec (CommRingCat.of R)) = t := Category.comp_id t
    have H := hclass t a
    convert H using 1 <;> simp only [N', postComp, curveChange]
    all_goals congr 1 <;> simp only [ht]
  · intro T t x y
    have ht : t ≫ 𝟙 (Spec (CommRingCat.of R)) = t := Category.comp_id t
    have H := hmul t x y
    convert H using 1
    all_goals try simp only [ht, N', postComp]
    all_goals congr 1 <;> simp only [ht]
  · intro T t
    apply Subtype.ext
    have ht : t ≫ 𝟙 (Spec (CommRingCat.of R)) = t := Category.comp_id t
    have H := hone t
    convert H using 1
    all_goals try simp only [ht, N', postComp]
    all_goals congr 1 <;> simp only [ht]
#print axioms solution
