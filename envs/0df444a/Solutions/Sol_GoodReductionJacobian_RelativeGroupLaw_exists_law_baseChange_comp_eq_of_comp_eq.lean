-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_law_baseChange_comp_eq_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f783b429-2570-526c-91f9-e06ae148d1a4

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_law_baseChange_comp_eq_of_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace LawRestrict

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem mul_val_congr (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem baseChange_compat (L : RelativeGroupLaw S f) {Z : Type} [CommRing Z] (ι : Spec (CommRingCat.of Z) ⟶ Spec (CommRingCat.of S))
    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of Z)) (P Q : SchemeHomOver t (pullback.snd f ι)) :
    ((L.baseChange ι).mul t P Q).1 ≫ pullback.fst f ι =
      (L.mul (t ≫ ι) ⟨P.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 := by
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  rfl

theorem clause1 (L : RelativeGroupLaw S f) {Z' Z'' : Type} [CommRing Z'] [CommRing Z'']
    (ι' : Spec (CommRingCat.of Z') ⟶ Spec (CommRingCat.of S)) (ι'' : Spec (CommRingCat.of Z'') ⟶ Spec (CommRingCat.of S))
    (σ : Spec (CommRingCat.of Z'') ⟶ Spec (CommRingCat.of Z')) (hσ : σ ≫ ι' = ι'')
    (L' : RelativeGroupLaw Z' (pullback.snd f ι')) (L'' : RelativeGroupLaw Z'' (pullback.snd f ι''))
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of Z')) (P Q : SchemeHomOver t' (pullback.snd f ι')),
        (L'.mul t' P Q).1 ≫ pullback.fst f ι' =
          (L.mul (t' ≫ ι') ⟨P.1 ≫ pullback.fst f ι', by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f ι', by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (hL'' : ∀ (T : Scheme.{0}) (t'' : T ⟶ Spec (CommRingCat.of Z'')) (P Q : SchemeHomOver t'' (pullback.snd f ι'')),
        (L''.mul t'' P Q).1 ≫ pullback.fst f ι'' =
          (L.mul (t'' ≫ ι'') ⟨P.1 ≫ pullback.fst f ι'', by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f ι'', by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (κ : pullback f ι'' ⟶ pullback f ι') (hκ₁ : κ ≫ pullback.fst f ι' = pullback.fst f ι'')
    (hκ₂ : κ ≫ pullback.snd f ι' = pullback.snd f ι'' ≫ σ)
    (T : Scheme.{0}) (t'' : T ⟶ Spec (CommRingCat.of Z'')) (P Q : SchemeHomOver t'' (pullback.snd f ι''))
    (P' Q' : SchemeHomOver (t'' ≫ σ) (pullback.snd f ι')) (hP' : P'.1 = P.1 ≫ κ) (hQ' : Q'.1 = Q.1 ≫ κ) :
    (L''.mul t'' P Q).1 ≫ κ = (L'.mul (t'' ≫ σ) P' Q').1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, hκ₁, hL'', hL']
    apply mul_val_congr
    · rw [Category.assoc, hσ]
    · show P.1 ≫ pullback.fst f ι'' = P'.1 ≫ pullback.fst f ι'
      rw [hP', Category.assoc, hκ₁]
    · show Q.1 ≫ pullback.fst f ι'' = Q'.1 ≫ pullback.fst f ι'
      rw [hQ', Category.assoc, hκ₁]
  · rw [Category.assoc, hκ₂, ← Category.assoc, (L''.mul t'' P Q).2, (L'.mul (t'' ≫ σ) P' Q').2]

end LawRestrict

open LawRestrict in
theorem solution
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] [Algebra S S'] [Algebra S S''] [Algebra S' S'']
    [IsScalarTower S S' S'']
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))))
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    ∃ L'' : RelativeGroupLaw S'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'')))),
      (∀ (T : Scheme.{0}) (t'' : T ⟶ Spec (CommRingCat.of S''))
          (P Q : SchemeHomOver t'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))),
          (L''.mul t'' P Q).1 ≫
              pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) ≫
                  Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
                (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                  ← IsScalarTower.algebraMap_eq]) =
            (L'.mul (t'' ≫ Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
              ⟨P.1 ≫ pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))
                  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) ≫
                    Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
                  (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    ← IsScalarTower.algebraMap_eq]),
                by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))
                  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) ≫
                    Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
                  (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    ← IsScalarTower.algebraMap_eq]),
                by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ (T : Scheme.{0}) (t'' : T ⟶ Spec (CommRingCat.of S''))
          (P Q : SchemeHomOver t'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))),
          (L''.mul t'' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) =
            (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'')))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) := by
  refine ⟨L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S S''))), fun T t'' P Q => ?_,
    fun T t'' P Q => baseChange_compat L _ T t'' P Q⟩
  exact clause1 L _ _ (Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]) L' _ hL'
    (fun T t P Q => baseChange_compat L _ T t P Q) _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) T t'' P Q _ _ rfl rfl

end S_GoodReductionJacobian_RelativeGroupLaw_exists_law_baseChange_comp_eq_of_comp_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_law_baseChange_comp_eq_of_comp_eq (solution)
