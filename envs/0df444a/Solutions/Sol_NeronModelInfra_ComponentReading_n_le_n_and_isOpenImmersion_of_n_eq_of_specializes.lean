-- Prove2me | solution 1 for NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f95af2dd-2f11-5d7a-9872-48017c3856cc

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
import Theorems.Thm_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
import Theorems.Thm_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
import Theorems.Thm_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange
import Theorems.Thm_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
import Theorems.Thm_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
import Theorems.Thm_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis
import Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_ComponentReading_n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
p2m_attr_erase "instance" "NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace FS

theorem formallySmooth_stalk_of_smooth
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] (y : Y)
    [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) :
    Algebra.FormallySmooth R (Y.presheaf.stalk y) := by
  classical
  let O := Y.presheaf.stalk y

  have hmor : CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial) ≫
        f.stalkMap y := by
    apply Spec.map_injective
    rw [← halg, Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hc : ∀ r : R, algebraMap R O r =
      (f.stalkMap y).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    intro r
    exact congrArg (fun φ : CommRingCat.of R ⟶ Y.presheaf.stalk y => φ.hom r) hmor

  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let A := Γ(Spec (CommRingCat.of R), ⊤)
  let B := Γ(Y, V)
  letI algAB : Algebra A B := (f.appLE ⊤ V le_top).hom.toAlgebra
  have hsAB : (f.appLE ⊤ V le_top).hom.Smooth :=
    HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  haveI : Algebra.Smooth A B := hsAB
  letI algRA : Algebra R A := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toAlgebra
  letI algRB : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.Smooth R A := by
    haveI : Algebra.Smooth R R := {}
    refine Algebra.Smooth.of_equiv (A := R) ?_
    exact AlgEquiv.ofBijective (Algebra.ofId R A)
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.bijective
  haveI : Algebra.Smooth R B := Algebra.Smooth.comp R A B

  let 𝔓 := hV.primeIdealOf ⟨y, hyV⟩
  letI algBO : Algebra B O := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hyV⟩ : V)
  haveI hloc : IsLocalization.AtPrime O 𝔓.asIdeal := hV.isLocalization_stalk ⟨y, hyV⟩
  have htow : ∀ r : R, algebraMap B O (algebraMap R B r) = algebraMap R O r := by
    intro r
    rw [hc r]
    change (Y.presheaf.germ V y hyV).hom ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (f.stalkMap y).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply _ (f.stalkMap y),
      Scheme.Hom.germ_stalkMap f ⊤ y trivial, Scheme.Hom.appLE, Category.assoc]
    erw [TopCat.Presheaf.germ_res]
  haveI : IsScalarTower R B O := IsScalarTower.of_algebraMap_eq fun r => (htow r).symm

  haveI : Algebra.FormallySmooth R B := inferInstance
  haveI : Algebra.FormallySmooth B O := Algebra.FormallySmooth.of_isLocalization (Rₘ := O) 𝔓.asIdeal.primeCompl
  exact Algebra.FormallySmooth.comp R B O

end FS

namespace Transport

theorem isDomain_and_isDiscreteValuationRing_stalk_opens
    {X : Scheme.{u}} (W : X.Opens) (x : ↥W)
    [IsDomain (X.presheaf.stalk x.1)] [IsDiscreteValuationRing (X.presheaf.stalk x.1)] :
    ∃ (_ : IsDomain ((W : Scheme.{u}).presheaf.stalk x)), IsDiscreteValuationRing ((W : Scheme.{u}).presheaf.stalk x) := by
  let r : ((W : Scheme.{u}).presheaf.stalk x) ≃+* X.presheaf.stalk x.1 := (W.stalkIso x).commRingCatIsoToRingEquiv
  haveI hD : IsDomain ((W : Scheme.{u}).presheaf.stalk x) := MulEquiv.isDomain (X.presheaf.stalk x.1) r.toMulEquiv
  refine ⟨hD, ?_⟩
  haveI : IsPrincipalIdealRing ((W : Scheme.{u}).presheaf.stalk x) :=
    IsPrincipalIdealRing.of_surjective r.symm.toRingHom r.symm.surjective
  haveI : IsLocalRing ((W : Scheme.{u}).presheaf.stalk x) :=
    IsLocalRing.of_surjective' r.symm.toRingHom r.symm.surjective
  refine ⟨?_⟩
  intro h
  have hF : IsField ((W : Scheme.{u}).presheaf.stalk x) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr h
  have hF' : IsField (X.presheaf.stalk x.1) := MulEquiv.isField hF r.symm.toMulEquiv
  exact IsDiscreteValuationRing.not_a_field' (R := X.presheaf.stalk x.1)
    (IsLocalRing.isField_iff_maximalIdeal_eq.mp hF')

theorem isFractionRing_and_formallySmooth_stalk_opens
    {X Y' : Scheme.{u}} (W : X.Opens) (v : (W : Scheme.{u}) ⟶ Y') (x : ↥W)
    [IsDomain (X.presheaf.stalk x.1)] [IsDomain ((W : Scheme.{u}).presheaf.stalk x)]
    (hfrac : letI φ := v.stalkMap x ≫ (W.stalkIso x).hom
      letI : Algebra (Y'.presheaf.stalk (v.base x)) (FractionRing (X.presheaf.stalk x.1)) :=
        ((algebraMap (X.presheaf.stalk x.1) (FractionRing (X.presheaf.stalk x.1))).comp φ.hom).toAlgebra
      IsFractionRing (Y'.presheaf.stalk (v.base x)) (FractionRing (X.presheaf.stalk x.1)))
    (hfs : letI φ := v.stalkMap x ≫ (W.stalkIso x).hom
      letI : Algebra (Y'.presheaf.stalk (v.base x)) (X.presheaf.stalk x.1) := φ.hom.toAlgebra
      Algebra.FormallySmooth (Y'.presheaf.stalk (v.base x)) (X.presheaf.stalk x.1)) :
    (letI _i1 : Algebra (Y'.presheaf.stalk (v.base x)) (FractionRing ((W : Scheme.{u}).presheaf.stalk x)) :=
        ((algebraMap ((W : Scheme.{u}).presheaf.stalk x) (FractionRing ((W : Scheme.{u}).presheaf.stalk x))).comp (v.stalkMap x).hom).toAlgebra;
      IsFractionRing (Y'.presheaf.stalk (v.base x)) (FractionRing ((W : Scheme.{u}).presheaf.stalk x))) ∧
    (letI _i2 : Algebra (Y'.presheaf.stalk (v.base x)) ((W : Scheme.{u}).presheaf.stalk x) := (v.stalkMap x).hom.toAlgebra;
      Algebra.FormallySmooth (Y'.presheaf.stalk (v.base x)) ((W : Scheme.{u}).presheaf.stalk x)) := by

  let O' := Y'.presheaf.stalk (v.base x)
  let SW := (W : Scheme.{u}).presheaf.stalk x
  let SX := X.presheaf.stalk x.1
  let r : SW ≃+* SX := (W.stalkIso x).commRingCatIsoToRingEquiv
  let ψ : O' →+* SW := (v.stalkMap x).hom
  let φ : O' →+* SX := (v.stalkMap x ≫ (W.stalkIso x).hom).hom
  have hφψ : ∀ a, φ a = r (ψ a) := fun a => rfl

  letI aX : Algebra O' SX := φ.toAlgebra
  letI aW : Algebra O' SW := ψ.toAlgebra
  letI aKX : Algebra O' (FractionRing SX) := ((algebraMap SX (FractionRing SX)).comp φ).toAlgebra
  letI aKW : Algebra O' (FractionRing SW) := ((algebraMap SW (FractionRing SW)).comp ψ).toAlgebra

  let eS : SX ≃ₐ[O'] SW := AlgEquiv.ofRingEquiv (f := r.symm) (fun a => by
    show r.symm (φ a) = ψ a
    rw [hφψ, r.symm_apply_apply])
  let eK : FractionRing SX ≃ₐ[O'] FractionRing SW :=
    AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv r.symm) (fun a => by
      show IsFractionRing.ringEquivOfRingEquiv r.symm (algebraMap SX (FractionRing SX) (φ a)) =
        algebraMap SW (FractionRing SW) (ψ a)
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, hφψ, r.symm_apply_apply])
  constructor
  · haveI : IsFractionRing O' (FractionRing SX) := hfrac
    exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors O') eK
  · haveI : Algebra.FormallySmooth O' SX := hfs
    exact Algebra.FormallySmooth.of_equiv eS

end Transport

namespace OrderCmp

p2m_open "NeronModelInfra.TopFormOrder"

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
  {d : ℕ} [SmoothOfRelativeDimension d gK]
  {ω : Γ(gK.topDifferentials d, ⊤)}

theorem lift_comp_genericFibreRestrict
    {Y Y' : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of R)) (fY' : Y' ⟶ Spec (CommRingCat.of R))
    (W : Y.Opens) (v : SchemeHomOver (W.ι ≫ fY) fY')
    {S : Scheme.{u}} (a : S ⟶ (W : Scheme.{u})) (b : S ⟶ Spec (CommRingCat.of K))
    (hab : (a ≫ v.1) ≫ fY' = b ≫ specGenericFibreInclusion R K) :
    pullback.lift (a ≫ v.1) b hab =
      pullback.lift a b (by rw [← hab, Category.assoc, v.2]) ≫ (genericFibreRestrict R K fY' (W.ι ≫ fY) v).1 := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, genericFibreRestrict_coe_comp_fst, ← Category.assoc, pullback.lift_fst]
  · rw [pullback.lift_snd, Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.lift_snd]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)
    (hgen : T'.y ⤳ u.1.base ⟨T.y, hyW⟩) :
    T'.n ≤ T.n ∧
    (T.n = T'.n → u.1.base ⟨T.y, hyW⟩ = T'.y ∧
      ∃ (W' : T.Y.Opens) (hW' : W' ≤ W), T.y ∈ W' ∧ IsOpenImmersion (T.Y.homOfLE hW' ≫ u.1)) := by
  classical

  letI := T.algebra
  letI := T.algebraK
  haveI := T.isScalarTower
  letI := T.algebraU
  letI := gK.sectionsAlgebra T.U
  haveI := T.isScalarTowerU
  let O := T.Y.presheaf.stalk T.y
  let F := FractionRing O
  let x : ↥W := ⟨T.y, hyW⟩
  let y₁ : ↥T'.Y := u.1.base x
  let O' := T'.Y.presheaf.stalk y₁
  let φ : O' ⟶ O := u.1.stalkMap x ≫ (W.stalkIso x).hom
  letI algO'O : Algebra O' O := φ.hom.toAlgebra
  letI algO'F : Algebra O' F := ((algebraMap O F).comp φ.hom).toAlgebra
  letI algRO' : Algebra R O' := stalkAlgebra T'.f y₁
  have halg₁ : T'.Y.fromSpecStalk y₁ ≫ T'.f = Spec.map (CommRingCat.ofHom (algebraMap R O')) :=
    fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra T'.f y₁
  have hy₁ : T'.f.base y₁ = IsLocalRing.closedPoint R := by
    change (u.1 ≫ T'.f).base x = _
    rw [u.2]
    exact T.hy

  obtain ⟨hdomO', hφinj, htowRO'O, hfracO'⟩ :=
    NeronModelInfra.ComponentReading.isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
      K T T' W hyW u hu
  haveI : IsDomain O' := hdomO'
  haveI : IsScalarTower R O' O := htowRO'O
  haveI : IsFractionRing O' F := hfracO'
  haveI : @IsScalarTower O' O F algO'O.toSMul Algebra.toSMul algO'F.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI instROF : @IsScalarTower R O' F Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change algebraMap R F r = algebraMap O F (φ.hom (algebraMap R O' r))
    rw [show φ.hom (algebraMap R O' r) = algebraMap R O r from (IsScalarTower.algebraMap_apply R O' O r).symm]
    exact IsScalarTower.algebraMap_apply R O F r

  obtain ⟨_, _, hlocRO, hidx⟩ :=
    NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes T.f T.y T.hy T.hmax T.halg
  haveI : IsLocalHom (algebraMap R O) := hlocRO
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq

  have hx' : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, T.U) F)) ≫ T.hU.fromSpec =
      (schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T'.Y.fromSpecStalk y₁, halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O'))) T'.f))
        T'.e).1 := by
    rw [T.hx]

    let q₀ : Spec O ⟶ (W : Scheme.{u}) := Spec.map (W.stalkIso x).hom ≫ (W : Scheme.{u}).fromSpecStalk x
    have hq₀ι : q₀ ≫ W.ι = T.Y.fromSpecStalk T.y := by
      change (Spec.map (W.stalkIso x).hom ≫ (W : Scheme.{u}).fromSpecStalk x) ≫ W.ι = T.Y.fromSpecStalk x.1
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk W.ι (x := x), ← Category.assoc, ← Spec.map_comp,
        ← Scheme.Opens.stalkIso_inv]
      erw [(W.stalkIso x).inv_hom_id, Spec.map_id, Category.id_comp]
      rfl
    have hq₀u : q₀ ≫ u.1 = Spec.map φ ≫ T'.Y.fromSpecStalk y₁ := by
      change (Spec.map (W.stalkIso x).hom ≫ (W : Scheme.{u}).fromSpecStalk x) ≫ u.1 =
        Spec.map (u.1.stalkMap x ≫ (W.stalkIso x).hom) ≫ T'.Y.fromSpecStalk (u.1.base x)
      rw [Spec.map_comp, Category.assoc, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    have hspecO'F : Spec.map (CommRingCat.ofHom (algebraMap O' F)) =
        Spec.map (CommRingCat.ofHom (algebraMap O F)) ≫ Spec.map φ := by
      rw [← Spec.map_comp]; rfl

    change ((pointGenericFibre (K := K) (K' := F) (⟨T.Y.fromSpecStalk T.y, T.halg⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O))) T.f)).1 ≫ T.e.1) =
      (pointGenericFibre (K := K) (K' := F) (⟨T'.Y.fromSpecStalk y₁, halg₁⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O'))) T'.f)).1 ≫ T'.e.1
    have hcompat : (Spec.map (CommRingCat.ofHom (algebraMap O F)) ≫ q₀) ≫ W.ι ≫ T.f =
        Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ specGenericFibreInclusion R K := by
      rw [Category.assoc, ← Category.assoc q₀, hq₀ι, T.halg, ← Spec.map_comp, specGenericFibreInclusion_eq, ← Spec.map_comp]
      congr 1
      change CommRingCat.ofHom ((algebraMap O F).comp (algebraMap R O)) = CommRingCat.ofHom ((algebraMap K F).comp (algebraMap R K))
      rw [← IsScalarTower.algebraMap_eq R O F, ← IsScalarTower.algebraMap_eq R K F]
    let pt : Spec (CommRingCat.of F) ⟶ pullback (W.ι ≫ T.f) (specGenericFibreInclusion R K) :=
      pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap O F)) ≫ q₀) (Spec.map (CommRingCat.ofHom (algebraMap K F)))
        (by rw [Category.assoc]; exact hcompat)
    have hT : (pointGenericFibre (K := K) (K' := F) (⟨T.Y.fromSpecStalk T.y, T.halg⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O))) T.f)).1 =
        pt ≫ (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 := by
      apply pullback.hom_ext
      · rw [pointGenericFibre_coe_comp_fst, Category.assoc, genericFibreRestrict_coe_comp_fst, ← Category.assoc,
          pullback.lift_fst, Category.assoc, hq₀ι]
      · rw [pointGenericFibre_coe_comp_snd, Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.lift_snd]
    have hT' : (pointGenericFibre (K := K) (K' := F) (⟨T'.Y.fromSpecStalk y₁, halg₁⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O'))) T'.f)).1 =
        pt ≫ (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 := by
      apply pullback.hom_ext
      · rw [pointGenericFibre_coe_comp_fst, Category.assoc, genericFibreRestrict_coe_comp_fst, ← Category.assoc,
          pullback.lift_fst, Category.assoc, hq₀u, hspecO'F, Category.assoc]
      · rw [pointGenericFibre_coe_comp_snd, Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.lift_snd]
    rw [hT, hT', Category.assoc, Category.assoc, hu]

  obtain ⟨b', w, hread⟩ :=
    NeronModelInfra.ComponentReading.exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
      ϖ hϖ K hω T' y₁ hy₁ hgen halg₁ F T.U T.hU T.isScalarTowerU hx' T.ωU T.hωU

  have hO : Ideal.map (algebraMap R O) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O := hidx.map_maximalIdeal
  have hσ : (letI := gK.sectionsAlgebra T.U; topFormMap K K Γ(XK, T.U) F d T.ωU) =
      (algebraMap O' F (w : O') * algebraMap O' F (algebraMap R O' ϖ) ^ T'.n) •
        topFormMap R K O' F d (exteriorPower.ιMulti O' d b') := hread
  obtain ⟨hle, hiff⟩ :=
    NeronModelInfra.TopFormOrder.le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
      R K O' O F ϖ hϖ hO d b' T.b T'.n w (letI := gK.sectionsAlgebra T.U; topFormMap K K Γ(XK, T.U) F d T.ωU) hσ

  have hordT : ord R K O d F (letI := gK.sectionsAlgebra T.U; topFormMap K K Γ(XK, T.U) F d T.ωU) = T.n := by
    obtain ⟨hρne, -⟩ := NeronModelInfra.TopFormOrder.topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq R K O F d T.b
    obtain ⟨-, hordsmul⟩ := NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis R K O F d T.b
    have := hordsmul T.a T.ha0 hρne
    rw [T.ha]
    exact this
  rw [hordT] at hle hiff
  refine ⟨hle, fun heq => ?_⟩
  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange R O' O) := hiff.mp heq

  haveI : Algebra.FormallySmooth R O := FS.formallySmooth_stalk_of_smooth T.f T.y T.halg
  haveI : Algebra.FormallyEtale O' O := Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange hbij
  have hfsO : Algebra.FormallySmooth O' O := inferInstance

  obtain ⟨hdomS, hdvrS⟩ := Transport.isDomain_and_isDiscreteValuationRing_stalk_opens W x
  haveI := hdomS
  haveI := hdvrS
  obtain ⟨hfracS, hfsS⟩ := Transport.isFractionRing_and_formallySmooth_stalk_opens W u.1 x hfracO' hfsO
  obtain ⟨hϖO'0, hϖO'prime⟩ :=
    AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint ϖ hϖ T'.f y₁ hy₁ halg₁
  haveI : LocallyOfFiniteType u.1 := by
    have : LocallyOfFiniteType (u.1 ≫ T'.f) := by rw [u.2]; infer_instance
    exact HasRingHomProperty.of_comp (P := @LocallyOfFiniteType) (fun _ _ h => RingHom.FiniteType.of_comp_finiteType h) this
  haveI : IsLocallyNoetherian T'.Y := LocallyOfFiniteType.isLocallyNoetherian T'.f
  obtain ⟨V, hxV, hVopen⟩ :=
    AlgebraicGeometry.exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
      u.1 x (algebraMap R O' ϖ) hϖO'0 hϖO'prime hfracS hfsS

  let W' : T.Y.Opens := W.ι ''ᵁ V
  have hW' : W' ≤ W := by
    rintro z ⟨z', -, rfl⟩; exact z'.2
  have hyW' : T.y ∈ W' := ⟨x, hxV, rfl⟩

  have hfac : T.Y.homOfLE hW' = (W.ι.isoImage V).inv ≫ V.ι := by
    rw [← cancel_mono W.ι, Scheme.homOfLE_ι, Category.assoc, Scheme.Hom.isoImage_inv_ι]
  haveI : IsOpenImmersion (V.ι ≫ u.1) := hVopen
  have hopen : IsOpenImmersion (T.Y.homOfLE hW' ≫ u.1) := by
    rw [hfac, Category.assoc]; infer_instance

  let ψ := V.ι ≫ u.1
  let pt : ↥V := ⟨x, hxV⟩
  have hψpt : ψ.base pt = y₁ := rfl
  have hmemr : T'.y ∈ Set.range ψ.base :=
    hgen.mem_open ψ.isOpenEmbedding.isOpen_range ⟨pt, hψpt⟩
  obtain ⟨z, hz⟩ := hmemr
  have hzpt : z ⤳ pt := by
    rw [← ψ.isOpenEmbedding.isEmbedding.isInducing.specializes_iff, hz, hψpt]; exact hgen
  have hzT : (V.ι ≫ W.ι).base z ⤳ T.y := hzpt.map (V.ι ≫ W.ι).base.hom.continuous
  have hzsp : T.f.base ((V.ι ≫ W.ι).base z) = IsLocalRing.closedPoint R := by
    change ((V.ι ≫ W.ι) ≫ T.f).base z = _
    rw [Category.assoc, ← u.2, ← Category.assoc]
    change T'.f.base (ψ.base z) = _
    rw [hz]; exact T'.hy
  have hzeq : (V.ι ≫ W.ι).base z = (V.ι ≫ W.ι).base pt := (T.hmax _ hzT hzsp).trans rfl
  have hz' : z = pt := (V.ι ≫ W.ι).isOpenEmbedding.injective hzeq
  refine ⟨?_, W', hW', hyW', hopen⟩
  change y₁ = T'.y
  rw [← hψpt, ← hz', hz]

end OrderCmp

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)
    (hgen : T'.y ⤳ u.1.base ⟨T.y, hyW⟩) :
    T'.n ≤ T.n ∧
    (T.n = T'.n → u.1.base ⟨T.y, hyW⟩ = T'.y ∧
      ∃ (W' : T.Y.Opens) (hW' : W' ≤ W), T.y ∈ W' ∧ IsOpenImmersion (T.Y.homOfLE hW' ≫ u.1)) :=
  OrderCmp.main K hω T T' W hyW u hu hgen

end S_NeronModelInfra_ComponentReading_n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
end P2MW
export P2MW.S_NeronModelInfra_ComponentReading_n_le_n_and_isOpenImmersion_of_n_eq_of_specializes (solution)
