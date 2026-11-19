-- Prove2me | solution 1 for NLabCohomology.characteristicClass
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:44:05.231684+00:00
-- url     : https://prove2.me/submissions/37f54ee2-e6e7-4f34-88c5-713dd13f4567

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

open NLabCohomology in
theorem solution (H : InfinityOneCategory.{u}) {X A B : H.Obj}
    (k : Cocycle H A B) :
    ∃ φ : Cohomology H X A → Cohomology H X B,
      ∀ c : Cocycle H X A,
        φ (cohomologyClass H c) = cohomologyClass H (charCocycle H c k) :=
  ⟨SSet.π₀.lift (fun c => cohomologyClass H (charCocycle H c k))
      (fun _ _ e => SSet.π₀.sound (NLabAux.edgeComp H e (SSet.Edge.id k))),
    fun c => SSet.π₀.lift_mk _ _ _⟩
