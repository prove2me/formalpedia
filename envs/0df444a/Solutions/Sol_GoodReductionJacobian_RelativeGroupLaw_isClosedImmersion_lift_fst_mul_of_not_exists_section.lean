-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_lift_fst_mul_of_not_exists_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0d8047e5-1c1d-521b-b462-c83d99912b4c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_Scheme_isClosed_range_of_not_exists_section_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_lift_fst_mul_of_not_exists_section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GRAPHCLOSED

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  set y := schemeHomOverComp ψ hψ (G.inv t x)
  set z := schemeHomOverComp ψ hψ x
  have hyz : G.mul t' y z = G.one t' := by
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural t t' ψ hψ]
  calc y = G.mul t' y (G.one t') := (G.mul_one t' y).symm
    _ = G.mul t' y (G.mul t' z (G.inv t' z)) := by rw [G.mul_inv_cancel]
    _ = G.mul t' (G.mul t' y z) (G.inv t' z) := by rw [G.mul_assoc]
    _ = G.inv t' z := by rw [hyz, G.one_mul]

end GRAPHCLOSED

open GRAPHCLOSED in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
    (hd : ¬ ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.1 = d.1) :
    IsClosedImmersion
      (pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl d)).1
        (pullback.condition.trans
          (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R K)))
            ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
            (GoodReductionJacobian.schemeHomOverComp
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl d)).2.symm) :
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ pullback f f) := by

  set tK : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ Spec (CommRingCat.of R) := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R K))) with htK
  set u : SchemeHomOver tK f := ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩ with hu
  set dT : SchemeHomOver tK f := GoodReductionJacobian.schemeHomOverComp (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl d with hdT

  set γ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ pullback f f := pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (L.mul tK u dT).1
      (pullback.condition.trans (L.mul tK u dT).2.symm) with hγ

  let t₂ : pullback f f ⟶ Spec (CommRingCat.of R) := pullback.fst f f ≫ f
  let a : SchemeHomOver t₂ f := ⟨pullback.fst f f, rfl⟩
  let b : SchemeHomOver t₂ f := ⟨pullback.snd f f, pullback.condition.symm⟩
  let σ : pullback f f ⟶ pullback f f := pullback.lift (pullback.fst f f) (L.mul t₂ (L.inv t₂ a) b).1
      (by rw [(L.mul t₂ (L.inv t₂ a) b).2])
  let τ : pullback f f ⟶ pullback f f := pullback.lift (pullback.fst f f) (L.mul t₂ a b).1 (by rw [(L.mul t₂ a b).2])
  have hσfst : σ ≫ pullback.fst f f = pullback.fst f f := pullback.lift_fst _ _ _
  have hσsnd : σ ≫ pullback.snd f f = (L.mul t₂ (L.inv t₂ a) b).1 := pullback.lift_snd _ _ _
  have hτfst : τ ≫ pullback.fst f f = pullback.fst f f := pullback.lift_fst _ _ _
  have hτsnd : τ ≫ pullback.snd f f = (L.mul t₂ a b).1 := pullback.lift_snd _ _ _
  have hσt : σ ≫ t₂ = t₂ := by show σ ≫ (pullback.fst f f ≫ f) = _; rw [← Category.assoc, hσfst]
  have hτt : τ ≫ t₂ = t₂ := by show τ ≫ (pullback.fst f f ≫ f) = _; rw [← Category.assoc, hτfst]
  have hσa : GoodReductionJacobian.schemeHomOverComp σ hσt a = a := Subtype.ext hσfst
  have hσb : GoodReductionJacobian.schemeHomOverComp σ hσt b = L.mul t₂ (L.inv t₂ a) b := Subtype.ext hσsnd
  have hτa : GoodReductionJacobian.schemeHomOverComp τ hτt a = a := Subtype.ext hτfst
  have hτb : GoodReductionJacobian.schemeHomOverComp τ hτt b = L.mul t₂ a b := Subtype.ext hτsnd
  have hστ : σ ≫ τ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hτfst, hσfst, Category.id_comp]
    · rw [Category.assoc, hτsnd, Category.id_comp]
      have h := congrArg Subtype.val (L.mul_natural t₂ t₂ σ hσt a b)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
      rw [h, hσa, hσb, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul]
  have hτσ : τ ≫ σ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσfst, hτfst, Category.id_comp]
    · rw [Category.assoc, hσsnd, Category.id_comp]
      have h := congrArg Subtype.val (L.mul_natural t₂ t₂ τ hτt (L.inv t₂ a) b)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
      rw [h, inv_natural L t₂ t₂ τ hτt a, hτa, hτb, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
  haveI : IsIso σ := ⟨⟨τ, hστ, hτσ⟩⟩

  set δ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ pullback f f := pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ d.1)
      (by rw [Category.assoc, d.2]; exact pullback.condition) with hδ
  have hγt : γ ≫ t₂ = tK := by
    show γ ≫ (pullback.fst f f ≫ f) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    rw [← Category.assoc, pullback.lift_fst]; exact pullback.condition
  have hγσ : γ ≫ σ = δ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσfst, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hσsnd, pullback.lift_snd]
      have h := congrArg Subtype.val (L.mul_natural t₂ tK γ hγt (L.inv t₂ a) b)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
      rw [h, inv_natural L t₂ tK γ hγt a]
      have hγa : GoodReductionJacobian.schemeHomOverComp γ hγt a = u := Subtype.ext (pullback.lift_fst _ _ _)
      have hγb : GoodReductionJacobian.schemeHomOverComp γ hγt b = L.mul tK u dT := Subtype.ext (pullback.lift_snd _ _ _)
      rw [hγa, hγb, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
      rfl

  haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  let s : Spec (CommRingCat.of K) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := pullback.lift d.1 (𝟙 _) (by rw [d.2, Category.id_comp])
  have hs : s ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) = 𝟙 _ := pullback.lift_snd _ _ _
  haveI : IsClosedImmersion (s ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
  have hds : d.1 = s ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := (pullback.lift_fst _ _ _).symm
  haveI : IsPreimmersion d.1 := by rw [hds]; infer_instance
  have hclosed : IsClosed (Set.range d.1.base) :=
    AlgebraicGeometry.Scheme.isClosed_range_of_not_exists_section_comp_eq K f d.1 d.2 (by
      rintro ⟨s', hs'1, hs'2⟩
      exact hd ⟨⟨s', hs'1⟩, hs'2⟩)
  haveI : IsClosedImmersion d.1 := IsClosedImmersion.of_isPreimmersion d.1 hclosed

  have hsq : IsPullback δ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (pullback.snd f f) d.1 := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f f)

    have h1 : δ ≫ pullback.fst f f = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := pullback.lift_fst _ _ _
    rw [h1, d.2]
    exact IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  haveI : IsClosedImmersion δ := IsClosedImmersion.isStableUnderBaseChange.of_isPullback hsq.flip inferInstance

  have hγeq : γ = δ ≫ inv σ := by rw [← hγσ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  show IsClosedImmersion γ
  rw [hγeq]
  infer_instance

end S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_lift_fst_mul_of_not_exists_section
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_lift_fst_mul_of_not_exists_section (solution)
