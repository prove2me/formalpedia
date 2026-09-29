-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.exists_section_toDR_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/061544b0-1f57-5168-b74a-f24b44d4742d

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_exists_section_toDR_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_exists_section_toDR_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq.AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage IsOpenImmersion.lift IsProper morphismRestrict_ι Scheme.Opens.range_ι IsProper.eq_valuativeCriterion specZIsTerminal ValuativeCommSq Spec Spec.map Scheme IsOpenImmersion Spec.map_injective Spec.preimage Spec.map_id IsAffineOpen Scheme.Opens ValuativeCriterion.Existence ValuativeCriterion IsOpenImmersion.lift_fac" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.exists_SpecMap_algebraMap_fixedField_comp_eq_of_forall_SpecMap_comp_eq
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (Γ : Subgroup (Ω ≃ₐ[k] Ω))
    {X : Scheme.{0}} (P : Spec (CommRingCat.of Ω) ⟶ X)
    (hP : ∀ g ∈ Γ, Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫ P = P) :
    ∃ P₁ : Spec (CommRingCat.of ↥(IntermediateField.fixedField Γ)) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap ↥(IntermediateField.fixedField Γ) Ω)) ≫ P₁ = P := by
  classical

  set x₀ : ↥X := P.base (IsLocalRing.closedPoint Ω) with hx₀
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  set U : X.Opens := U' with hUdef
  have hU : IsAffineOpen U := hU'

  have hrange : Set.range P.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    rw [Scheme.Opens.range_ι]
    exact hxU
  set Q : Spec (CommRingCat.of Ω) ⟶ ↑U := IsOpenImmersion.lift U.ι P hrange with hQ
  have hQfac : Q ≫ U.ι = P := IsOpenImmersion.lift_fac U.ι P hrange

  set φ : Γ(X, U) ⟶ CommRingCat.of Ω := Spec.preimage (Q ≫ hU.isoSpec.hom) with hφ
  have hφQ : Spec.map φ = Q ≫ hU.isoSpec.hom := Spec.map_preimage _
  have hφP : Spec.map φ ≫ hU.isoSpec.inv ≫ U.ι = P := by
    rw [hφQ, Category.assoc, Iso.hom_inv_id_assoc, hQfac]

  have hφinv : ∀ g ∈ Γ, φ ≫ CommRingCat.ofHom (g : Ω →+* Ω) = φ := by
    intro g hg
    apply Spec.map_injective
    rw [Spec.map_comp]

    have hmono : Mono (hU.isoSpec.inv ≫ U.ι) := inferInstance
    rw [← cancel_mono (hU.isoSpec.inv ≫ U.ι), Category.assoc, hφP]
    exact hP g hg
  have hmem : ∀ r : Γ(X, U), φ.hom r ∈ IntermediateField.fixedField Γ := by
    intro r
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have := congrArg (fun ψ => ψ.hom r) (hφinv g hg)
    simpa using this

  let φ₁ : Γ(X, U) →+* ↥(IntermediateField.fixedField Γ) :=
    { toFun := fun r => ⟨φ.hom r, hmem r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hφ₁ : (algebraMap ↥(IntermediateField.fixedField Γ) Ω).comp φ₁ = φ.hom := RingHom.ext fun r => rfl
  refine ⟨Spec.map (CommRingCat.ofHom φ₁) ≫ hU.isoSpec.inv ≫ U.ι, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ₁, CommRingCat.ofHom_hom]
  exact hφP

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ModularCurve ModularCurve.DRResolvedModelPackage in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      ePl (arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V) = arithmeticGalois (modularFunctionFieldFull p) σ • ePl V)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (hV : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) :
    ∃ t : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase,
      Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ t.1 ≫ 𝔛reg.toDR ≫
          pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
        ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ := by
  classical

  set x := (𝔛.Mη.pointEquivPlace).symm (ePl V) with hxdef
  have hxV : 𝔛.Mη.pointEquivPlace x = ePl V := by rw [hxdef, Equiv.apply_symm_apply]

  have hinv : ∀ g ∈ A.inertiaSubgroupIn ℚ,
      Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔛.eη ≫ pullback.fst _ _ =
        x.1 ≫ 𝔛.eη ≫ pullback.fst _ _ := by
    intro g hg
    haveI := 𝔛.eη_iso

    have hw : (Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔛.eη ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ≫ DRModel.toBase p =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) :=
      specZIsTerminal.hom_ext _ _
    let x'' := pullback.lift _ _ hw
    have hx''snd : x'' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hx''fst : x'' ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔛.eη ≫ pullback.fst _ _ :=
      pullback.lift_fst _ _ _
    let x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _} :=
      ⟨x'' ≫ inv 𝔛.eη, by rw [← 𝔛.heη, Category.assoc, IsIso.inv_hom_id_assoc, hx''snd]⟩
    have hx' : x'.1 ≫ 𝔛.eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔛.eη ≫ pullback.fst _ _ := by
      show (x'' ≫ inv 𝔛.eη) ≫ 𝔛.eη ≫ pullback.fst _ _ = _
      rw [Category.assoc, IsIso.inv_hom_id_assoc, hx''fst]
    have hgal := 𝔛.hgal g x x' hx'
    rw [hxV, ← hePl_gal, hV g hg, ← hxV] at hgal
    have hxx : x' = x := 𝔛.Mη.pointEquivPlace.injective hgal
    rw [← hx', hxx]

  obtain ⟨P₁, hP₁⟩ := AlgebraicGeometry.exists_SpecMap_algebraMap_fixedField_comp_eq_of_forall_SpecMap_comp_eq
    (A.inertiaSubgroupIn ℚ) (x.1 ≫ 𝔛.eη ≫ pullback.fst _ _) (fun g hg => by
      simpa only [Category.assoc] using hinv g hg)

  let Kf := ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
  let R' : ValuationSubring Kf := A.comap (algebraMap Kf (AlgebraicClosure ℚ))
  let jO : O →+* Kf := R'.subtype.comp eO.toRingHom

  have hwC : P₁ ≫ DRModel.toBase p = Spec.map (CommRingCat.ofHom jO) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) :=
    specZIsTerminal.hom_ext _ _
  let y₀ := pullback.lift _ _ hwC
  have hy₀fst : y₀ ≫ pullback.fst _ _ = P₁ := pullback.lift_fst _ _ _
  have hy₀snd : y₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom jO) := pullback.lift_snd _ _ _

  let W : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens :=
    pullback.snd (DRModel.toBase p) _ ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)
  have hjO : Function.Injective jO := Subtype.val_injective.comp eO.injective
  have hrange : Set.range ⇑y₀.base ⊆ (W : Set _) := by
    rintro _ ⟨pt, rfl⟩
    show (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base (y₀.base pt) ∈
      PrimeSpectrum.basicOpen ((p : ℕ) : O)
    rw [show (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base (y₀.base pt) =
        (y₀ ≫ pullback.snd _ _).base pt from rfl, hy₀snd]
    change ((p : ℕ) : O) ∉ Ideal.comap jO pt.asIdeal
    have hpt : pt.asIdeal = ⊥ := by
      rcases Ideal.eq_bot_or_top pt.asIdeal with h | h
      · exact h
      · exact absurd h pt.isPrime.ne_top
    rw [hpt, Ideal.mem_comap, Ideal.mem_bot, map_natCast]
    exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let y₀' := IsOpenImmersion.lift W.ι y₀ (by rw [Scheme.Opens.range_ι]; exact hrange)
  have hy₀' : y₀' ≫ W.ι = y₀ := IsOpenImmersion.lift_fac _ _ _
  haveI := 𝔛reg.toDR_iso_generic
  let y : Spec (CommRingCat.of Kf) ⟶ 𝔛reg.Y := y₀' ≫ inv (𝔛reg.toDR ∣_ W) ≫ (𝔛reg.toDR ⁻¹ᵁ W).ι
  have hy : y ≫ 𝔛reg.toDR = y₀ := by
    show (y₀' ≫ inv (𝔛reg.toDR ∣_ W) ≫ (𝔛reg.toDR ⁻¹ᵁ W).ι) ≫ 𝔛reg.toDR = y₀
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hy₀']

  haveI := 𝔛reg.isProper
  have hex : ValuativeCriterion.Existence 𝔛reg.toBase :=
    (IsProper.eq_valuativeCriterion ▸ (inferInstance : IsProper 𝔛reg.toBase)).1.1.1.existence
  have hsq : CommSq y (Spec.map (CommRingCat.ofHom (algebraMap R' Kf))) 𝔛reg.toBase
      (Spec.map (CommRingCat.ofHom eO.toRingHom)) := by
    constructor
    rw [← 𝔛reg.toDR_over, ← Category.assoc, hy, hy₀snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let S : ValuativeCommSq 𝔛reg.toBase := { R := R', K := Kf, i₁ := y, i₂ := Spec.map (CommRingCat.ofHom eO.toRingHom), commSq := hsq }
  haveI : S.commSq.HasLift := hex S
  let ℓ := S.commSq.lift
  have hℓ₁ : Spec.map (CommRingCat.ofHom (algebraMap R' Kf)) ≫ ℓ = y := S.commSq.fac_left
  have hℓ₂ : ℓ ≫ 𝔛reg.toBase = Spec.map (CommRingCat.ofHom eO.toRingHom) := S.commSq.fac_right

  refine ⟨⟨Spec.map (CommRingCat.ofHom eO.symm.toRingHom) ≫ ℓ, ?_⟩, ?_⟩
  · rw [Category.assoc, hℓ₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : eO.symm.toRingHom.comp eO.toRingHom = RingHom.id O := by
      ext a; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  · show Spec.map (CommRingCat.ofHom ((algebraMap Kf (AlgebraicClosure ℚ)).comp jO)) ≫
        (Spec.map (CommRingCat.ofHom eO.symm.toRingHom) ≫ ℓ) ≫ 𝔛reg.toDR ≫ pullback.fst _ _ = x.1 ≫ 𝔛.eη ≫ pullback.fst _ _
    have h1 : Spec.map (CommRingCat.ofHom ((algebraMap Kf (AlgebraicClosure ℚ)).comp jO)) ≫
        Spec.map (CommRingCat.ofHom eO.symm.toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap Kf (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R' Kf)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      simp [jO]
    rw [Category.assoc, ← Category.assoc (Spec.map _) (Spec.map _), h1, Category.assoc,
      ← Category.assoc (Spec.map (CommRingCat.ofHom (algebraMap (↥R') Kf))), hℓ₁, ← Category.assoc y, hy]
    rw [hy₀fst, hP₁]

end S_ModularCurve_DRResolvedModelPackage_exists_section_toDR_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_exists_section_toDR_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq (solution)
