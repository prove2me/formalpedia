-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e7d27297-ef45-5211-86cd-e1efe245bcc9

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

namespace InvPts_d51776f2

theorem mul_castOver {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (a b : SchemeHomOver ι f) :
    G.mul ι' (castOver h a) (castOver h b) = castOver h (G.mul ι a b) := by
  subst h; rfl

theorem castOver_coe {B T X : Scheme.{0}} {ι ι' : T ⟶ B} {f : X ⟶ B} (h : ι = ι') (x : SchemeHomOver ι f) :
    (castOver h x).1 = x.1 := rfl

theorem shGenLift_coe_fst {N₀ p : ℕ} [NeZero N₀] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) {X : Scheme.{0}} {f : X ⟶ base p} (y : SchemeHomOver (genPt p) f) :
    (Λ.shGenLift y).1 ≫ pullback.fst f Λ.shStr = y.1 := by
  simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  rfl

end InvPts_d51776f2

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    ∃ yK : ↥(inertiaInvariants A (N₀ * p)) →
        SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
      (∀ x, Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫ (yK x).1 =
          (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1) ∧
      (∀ x x', yK (x + x') = (O.L.baseChange Λ.shStr).mul _ (yK x) (yK x')) ∧
      Function.Bijective yK := by
  classical
  haveI : IsSeparated O.g := O.separated

  have hbar : barPt A ≫ shPt A =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫
        specGenericFibreInclusion ↥(shRing A) ↥(invField A) := by
    rw [specGenericFibreInclusion_eq, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    rfl

  have hσbar : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) := by
    intro σ hσ
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext k
    exact (IntermediateField.mem_fixedField_iff (A.inertiaSubgroupIn ℚ) (k : AlgebraicClosure ℚ)).1 k.2 σ hσ
  have hσcoe : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) = σ.toRingEquiv.toRingHom := fun σ => rfl

  have hz : ∀ (x : ↥(inertiaInvariants A (N₀ * p))), ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv.toRingHom) ≫
          (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 =
        (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 := by
    intro x σ hσ
    have hx : σ • (x : JZero (N₀ * p)) = x := x.2 σ hσ
    have hg := O.pts_galois σ (x : JZero (N₀ * p))
    rw [hx, hσcoe] at hg
    apply pullback.hom_ext
    · rw [Category.assoc]
      erw [pullback.lift_fst]
      exact hg.symm
    · rw [Category.assoc]
      erw [pullback.lift_snd]
      rw [hbar, ← Category.assoc, hσbar σ hσ]

  have hdesc : ∀ x : ↥(inertiaInvariants A (N₀ * p)), ∃ y : Spec (CommRingCat.of ↥(invField A)) ⟶ _,
      Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫ y =
        (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 := fun x =>
    AlgebraicGeometry.Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq (A.inertiaSubgroupIn ℚ)
      (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 (hz x)
  choose y hy using hdesc

  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ)))) :=
    ⟨fun q => ⟨default, Subsingleton.elim _ _⟩⟩
  have hover : ∀ x, y x ≫ RelativeGroupLaw.baseChangeStr Λ.shStr O.g =
      specGenericFibreInclusion ↥(shRing A) ↥(invField A) := by
    intro x
    apply AlgebraicGeometry.ext_of_isDominant
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))))
    rw [← Category.assoc, hy x, (Λ.shGenLift _).2, hbar]
  refine ⟨fun x => ⟨y x, hover x⟩, fun x => hy x, ?_, ?_, ?_⟩
  ·
    intro x x'
    apply Subtype.ext
    refine AlgebraicGeometry.ext_of_isDominant_of_isSeparated (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) ?_
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ)))) ?_
    · rw [hover]; exact (((O.L.baseChange Λ.shStr).mul _ ⟨y x, hover x⟩ ⟨y x', hover x'⟩).2).symm
    · change Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫ y (x + x') = _
      rw [hy]
      have key := congrArg Subtype.val ((O.L.baseChange Λ.shStr).mul_natural
        (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) _
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ)))) rfl ⟨y x, hover x⟩ ⟨y x', hover x'⟩)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at key
      rw [key]
      have hX : ∀ z : ↥(inertiaInvariants A (N₀ * p)),
          GoodReductionJacobian.schemeHomOverComp
              (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ)))) rfl ⟨y z, hover z⟩ =
            castOver hbar (Λ.shGenLift (O.pts (z : JZero (N₀ * p)))) := fun z => Subtype.ext (hy z)
      rw [hX x, hX x', InvPts_d51776f2.mul_castOver, InvPts_d51776f2.castOver_coe]
      have hadd : ((x + x' : ↥(inertiaInvariants A (N₀ * p))) : JZero (N₀ * p)) = (x : JZero (N₀ * p)) + x' :=
        AddSubgroup.coe_add _ _ _
      rw [hadd, O.pts_add]
      simp only [LevelData.shGenLift, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase,
        InvPts_d51776f2.mul_castOver]
  ·
    intro x x' hxx
    have h1 : (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 = (Λ.shGenLift (O.pts (x' : JZero (N₀ * p)))).1 := by
      rw [← hy, ← hy]; exact congrArg (fun u => Spec.map _ ≫ u.1) hxx
    have h2 : (O.pts (x : JZero (N₀ * p))).1 = (O.pts (x' : JZero (N₀ * p))).1 := by
      rw [← InvPts_d51776f2.shGenLift_coe_fst Λ (O.pts (x : JZero (N₀ * p))), h1, InvPts_d51776f2.shGenLift_coe_fst]
    have h3 : (x : JZero (N₀ * p)) = x' := O.pts.injective (Subtype.ext h2)
    exact Subtype.ext h3

  ·
    intro u
    have e : (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫
        specGenericFibreInclusion ↥(shRing A) ↥(invField A)) ≫ Λ.shStr = genPt p := by
      rw [← hbar]; exact Λ.barPt_shPt_shStr
    let w : SchemeHomOver (genPt p) O.g := castOver e (RelativeGroupLaw.baseChangePointToBase Λ.shStr
      (GoodReductionJacobian.schemeHomOverComp
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ)))) rfl u))
    have hw : w.1 = (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫ u.1) ≫
        pullback.fst O.g Λ.shStr := rfl
    have hx₀ : O.pts.symm w ∈ inertiaInvariants A (N₀ * p) := by
      rw [mem_inertiaInvariants]
      intro σ hσ
      apply O.pts.injective
      apply Subtype.ext
      rw [O.pts_galois, Equiv.apply_symm_apply, hσcoe, hw, ← Category.assoc, ← Category.assoc, hσbar σ hσ]
    refine ⟨⟨O.pts.symm w, hx₀⟩, ?_⟩
    apply Subtype.ext
    refine AlgebraicGeometry.ext_of_isDominant_of_isSeparated (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) ?_
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ)))) ?_
    · rw [hover]; exact u.2.symm
    · change Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫ y _ = _
      rw [hy]
      have hpw : O.pts ((⟨O.pts.symm w, hx₀⟩ : ↥(inertiaInvariants A (N₀ * p))) : JZero (N₀ * p)) = w :=
        O.pts.apply_symm_apply w
      rw [hpw]
      apply pullback.hom_ext
      · simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst, InvPts_d51776f2.castOver_coe,
          Category.assoc]
        rfl
      · simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd, Category.assoc]
        rw [hbar]
        congr 1
        exact u.2.symm

end S_ModularCurve_JZeroNeronObjectAtP_exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective (solution)
