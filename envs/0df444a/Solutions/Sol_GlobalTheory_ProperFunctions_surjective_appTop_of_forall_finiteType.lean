-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.surjective_appTop_of_forall_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:52.206286+00:00
-- url     : https://prove2.me/submissions/28e0d3c4-fc5c-4854-86e1-6ffd8d180263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {p : X ⟶ Spec (.of R)} [QuasiCompact p] [QuasiSeparated p]
    (h : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Function.Surjective
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    {g : Y ⟶ X} {q : Y ⟶ Spec (.of A)}
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Function.Surjective q.appTop := by
  classical
  let F : Finset A ⥤ CommRingCat.{u} :=
    { obj s := .of (Algebra.adjoin R (s : Set A))
      map {s t} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cF : Cocone F :=
    { pt := .of A
      ι := { app s := CommRingCat.ofHom (Algebra.adjoin R (s : Set A)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcF : IsColimit cF := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : A := x
        exact ⟨({x'} : Finset A), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin R (({x'} : Finset A) : Set A)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset A)ᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cF.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcF.op
  let ι (s : (Finset A)ᵒᵖ) : G.obj s ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R (s.unop : Set A))))
  have hι {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : G.map f ≫ ι t = ι s := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hι' (s : (Finset A)ᵒᵖ) :
      cG.π.app s ≫ ι s = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let D : (Finset A)ᵒᵖ ⥤ Scheme.{u} :=
    { obj s := pullback p (ι s)
      map {s t} f := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ G.map f)
        (by rw [Category.assoc, hι, pullback.condition])
      map_id s := by apply pullback.hom_ext <;> simp
      map_comp f f' := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
            G.map_comp, Category.assoc] }
  let α : D ⟶ G :=
    { app s := pullback.snd p (ι s)
      naturality s t f := pullback.lift_snd _ _ _ }
  let π (s : (Finset A)ᵒᵖ) : Y ⟶ pullback p (ι s) :=
    pullback.lift g (q ≫ cG.π.app s) (by rw [Category.assoc, hι', H.w])
  let cD : Cone D :=
    { pt := Y
      π :=
        { app := π
          naturality s t f := by
            change 𝟙 Y ≫ π t = π s ≫ pullback.lift _ _ _
            apply pullback.hom_ext
            · rw [Category.id_comp, Category.assoc, pullback.lift_fst, pullback.lift_fst,
                pullback.lift_fst]
            · rw [Category.id_comp, Category.assoc, pullback.lift_snd, pullback.lift_snd,
                pullback.lift_snd_assoc, Category.assoc, cG.w f] } }
  have hπ (s : (Finset A)ᵒᵖ) : IsPullback (π s) q (pullback.snd p (ι s)) (cG.π.app s) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (ι s)) (v₁₃ := p) (h₂₂ := ι s) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [hι', pullback.lift_fst]
    exact H
  have hcD : IsLimit cD := isLimitOfIsPullbackOfIsConnected α cD cG
    { hom := q, w s := (pullback.lift_snd _ _ _).symm } hπ hcG
  have hG (s : (Finset A)ᵒᵖ) : IsAffine (G.obj s) := inferInstanceAs (IsAffine (Spec _))
  have {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (D.map f) := by
    have : IsPullback (D.map f) (pullback.snd p (ι s)) (pullback.snd p (ι t)) (G.map f) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst p (ι t)) (v₁₃ := p) (h₂₂ := ι t) ?_
        (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
      rw [hι, pullback.lift_fst]
      exact .of_hasPullback _ _
    exact MorphismProperty.of_isPullback this.flip inferInstance
  have (s : (Finset A)ᵒᵖ) : CompactSpace (D.obj s) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p (ι s))
  have (s : (Finset A)ᵒᵖ) : QuasiSeparatedSpace (D.obj s) :=
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p (ι s))).mp inferInstance
  intro x
  obtain ⟨s, y, rfl⟩ := exists_appTop_π_eq_of_isLimit D cD hcD x
  have : Algebra.FiniteType R (Algebra.adjoin R (s.unop : Set A)) :=
    Algebra.FiniteType.adjoin_of_finite s.unop.finite_toSet
  obtain ⟨b, rfl⟩ := h (Algebra.adjoin R (s.unop : Set A)) y
  refine ⟨(cG.π.app s).appTop b, ?_⟩
  have := congr(($((hπ s).w)).appTop b)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this
  exact this.symm
end GlobalTheory.ProperFunctions
