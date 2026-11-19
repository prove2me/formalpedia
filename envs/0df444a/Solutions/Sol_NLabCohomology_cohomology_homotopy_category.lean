-- Prove2me | solution 1 for NLabCohomology.cohomology_homotopy_category
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:44:06.32921+00:00
-- url     : https://prove2.me/submissions/db58f834-669f-4c89-acc7-804d804fa757

import Definitions.Def_NLabCohomology_Cohomology

universe u

open CategoryTheory Simplicial Opposite

namespace NLabAux

open SSet NLabCohomology

lemma hom00 (f : ⦋0⦌ ⟶ ⦋0⦌) : f = 𝟙 _ := by
  ext i
  fin_cases i
  simp

variable (H : InfinityOneCategory.{u})

lemma face_comp {X Y Z : H.Obj} (i : Fin 2) (a : H.hom X Y _⦋1⦌) (b : H.hom Y Z _⦋1⦌) :
    (H.hom X Z).δ i (H.comp a b) = H.comp ((H.hom X Y).δ i a) ((H.hom Y Z).δ i b) :=
  (H.comp_map (SimplexCategory.δ i) a b).symm

def edgeComp {X Y Z : H.Obj} {c₁ c₂ : H.hom X Y _⦋0⦌} {d₁ d₂ : H.hom Y Z _⦋0⦌}
    (e : (H.hom X Y).Edge c₁ c₂) (e' : (H.hom Y Z).Edge d₁ d₂) :
    (H.hom X Z).Edge (H.comp c₁ d₁) (H.comp c₂ d₂) :=
  Edge.mk (H.comp e.edge e'.edge)
    (by rw [face_comp, e.src_eq, e'.src_eq])
    (by rw [face_comp, e.tgt_eq, e'.tgt_eq])

lemma id_comp0 {X Y : H.Obj} (c : H.hom X Y _⦋0⦌) : H.comp (H.id X) c = c := by
  have := H.id_comp (n := 0) c
  rwa [hom00 (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0), op_id, Functor.map_id_apply] at this

lemma comp_id0 {X Y : H.Obj} (c : H.hom X Y _⦋0⦌) : H.comp c (H.id Y) = c := by
  have := H.comp_id (n := 0) c
  rwa [hom00 (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0), op_id, Functor.map_id_apply] at this

end NLabAux

open NLabCohomology SSet in
theorem solution (H : InfinityOneCategory.{u}) :
    ∃ comp : ∀ (X Y Z : H.Obj), Cohomology H X Y → Cohomology H Y Z → Cohomology H X Z,
      (∀ (X Y : H.Obj) (f : Cohomology H X Y),
        comp X X Y (cohomologyClass H (H.id X)) f = f) ∧
      (∀ (X Y : H.Obj) (f : Cohomology H X Y),
        comp X Y Y f (cohomologyClass H (H.id Y)) = f) ∧
      (∀ (W X Y Z : H.Obj) (f : Cohomology H W X) (g : Cohomology H X Y)
        (h : Cohomology H Y Z),
        comp W Y Z (comp W X Y f g) h = comp W X Z f (comp X Y Z g h)) ∧
      (∀ (X Y Z : H.Obj) (c : Cocycle H X Y) (d : Cocycle H Y Z),
        comp X Y Z (cohomologyClass H c) (cohomologyClass H d) =
          cohomologyClass H (H.comp c d)) := by
  let comp : ∀ (X Y Z : H.Obj), Cohomology H X Y → Cohomology H Y Z → Cohomology H X Z :=
    fun X Y Z f g =>
      π₀.lift (T := π₀ (H.hom X Z)) (fun c : H.hom X Y _⦋0⦌ =>
        π₀.lift (T := π₀ (H.hom X Z)) (fun d : H.hom Y Z _⦋0⦌ => (π₀.mk (H.comp c d) : π₀ (H.hom X Z)))
          (fun _ _ e => π₀.sound (NLabAux.edgeComp H (Edge.id c) e)) g)
        (fun c₁ c₂ e => by
          obtain ⟨d, rfl⟩ := π₀.mk_surjective g
          rw [π₀.lift_mk, π₀.lift_mk]
          exact π₀.sound (NLabAux.edgeComp H e (Edge.id d))) f
  have hmk : ∀ (X Y Z : H.Obj) (c : H.hom X Y _⦋0⦌) (d : H.hom Y Z _⦋0⦌),
      comp X Y Z (π₀.mk c) (π₀.mk d) = π₀.mk (H.comp c d) := by
    intro X Y Z c d
    simp only [comp]
    rw [π₀.lift_mk, π₀.lift_mk]
  refine ⟨comp, ?_, ?_, ?_, fun X Y Z c d => hmk X Y Z c d⟩
  · intro X Y f
    obtain ⟨c, rfl⟩ := π₀.mk_surjective f
    rw [cohomologyClass, hmk, NLabAux.id_comp0]
  · intro X Y f
    obtain ⟨c, rfl⟩ := π₀.mk_surjective f
    rw [cohomologyClass, hmk, NLabAux.comp_id0]
  · intro W X Y Z f g h
    obtain ⟨a, rfl⟩ := π₀.mk_surjective f
    obtain ⟨b, rfl⟩ := π₀.mk_surjective g
    obtain ⟨c, rfl⟩ := π₀.mk_surjective h
    rw [hmk, hmk, hmk, hmk, H.assoc]
