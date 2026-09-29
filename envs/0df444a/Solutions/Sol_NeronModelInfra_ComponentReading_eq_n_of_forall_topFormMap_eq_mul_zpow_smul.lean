-- Prove2me | solution 1 for NeronModelInfra.ComponentReading.eq_n_of_forall_topFormMap_eq_mul_zpow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d0baccfd-c02d-5ff0-ad1a-3905d620970a

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import Theorems.Thm_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
import Theorems.Thm_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis
import Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_isLocalization_atPrime_stalk_of_specializes
import Theorems.Thm_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_ComponentReading_eq_n_of_forall_topFormMap_eq_mul_zpow_smul
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mOrderId

theorem comp_algebraMap_eq_of_specializes {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) {y y₁ : Y} (h : y ⤳ y₁)
    [Algebra R (Y.presheaf.stalk y₁)] [Algebra R (Y.presheaf.stalk y)]
    (halg₁ : Y.fromSpecStalk y₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y₁))))
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) :
    (Y.presheaf.stalkSpecializes h).hom.comp (algebraMap R (Y.presheaf.stalk y₁)) =
      algebraMap R (Y.presheaf.stalk y) := by
  have key : CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y₁)) ≫ Y.presheaf.stalkSpecializes h =
      CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← halg, ← halg₁, ← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have := congrArg CommRingCat.Hom.hom key
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using this

end P2mOrderId

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T : ComponentReading R K gK d ω)
    (y₁ : ↥T.Y) (hy₁ : T.f.base y₁ = IsLocalRing.closedPoint R) (hgen : T.y ⤳ y₁)
    [Algebra R (T.Y.presheaf.stalk y₁)]
    (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))))
    (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
    (w : (T.Y.presheaf.stalk y₁)ˣ) (m : ℤ)
    (h : ∀ (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
        [IsScalarTower R (T.Y.presheaf.stalk y₁) F] [IsScalarTower R K F]
        (U : XK.Opens) (hU : IsAffineOpen U) [Algebra Γ(XK, U) F]
        (hKU : letI := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) F)
        (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) F)) ≫ hU.fromSpec =
          (schemeHomOverComp
            (pointGenericFibre (K := K) (K' := F)
              (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
                SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
            T.e).1)
        (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
        (hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω),
        letI := gK.sectionsAlgebra U
        TopFormOrder.topFormMap K K Γ(XK, U) F d ωU =
          (algebraMap (T.Y.presheaf.stalk y₁) F (w : (T.Y.presheaf.stalk y₁)) *
              algebraMap (T.Y.presheaf.stalk y₁) F (algebraMap R (T.Y.presheaf.stalk y₁) ϖ) ^ m) •
            TopFormOrder.topFormMap R K (T.Y.presheaf.stalk y₁) F d
              (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b')) :
    m = T.n := by
  classical

  letI algRO : Algebra R (T.Y.presheaf.stalk T.y) := T.algebra
  letI algKF : Algebra K (FractionRing (T.Y.presheaf.stalk T.y)) := T.algebraK
  haveI towRKF : IsScalarTower R K (FractionRing (T.Y.presheaf.stalk T.y)) := T.isScalarTower

  letI algO₁O : Algebra (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y) :=
    (T.Y.presheaf.stalkSpecializes hgen).hom.toAlgebra
  have hcomp := P2mOrderId.comp_algebraMap_eq_of_specializes T.f hgen halg₁ T.halg
  haveI towRO₁O : IsScalarTower R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y) :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm

  haveI towO₁OF : IsScalarTower (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)
      (FractionRing (T.Y.presheaf.stalk T.y)) := inferInstance
  haveI towRO₁F : IsScalarTower R (T.Y.presheaf.stalk y₁) (FractionRing (T.Y.presheaf.stalk T.y)) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [IsScalarTower.algebraMap_apply (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)
        (FractionRing (T.Y.presheaf.stalk T.y)),
      IsScalarTower.algebraMap_apply R (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)),
      ← IsScalarTower.algebraMap_apply R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)]

  haveI hdom₁ : IsDomain (T.Y.presheaf.stalk y₁) :=
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R T.f y₁).1
  haveI hlocO := AlgebraicGeometry.Scheme.isLocalization_atPrime_stalk_of_specializes (X := T.Y) hgen
  let P : Ideal (T.Y.presheaf.stalk y₁) :=
    Ideal.comap (T.Y.presheaf.stalkSpecializes hgen).hom (IsLocalRing.maximalIdeal (T.Y.presheaf.stalk T.y))
  haveI hfrac₁ : IsFractionRing (T.Y.presheaf.stalk y₁) (FractionRing (T.Y.presheaf.stalk T.y)) := by
    have h1 := IsLocalization.localization_localization_isLocalization_of_has_all_units
      (R := T.Y.presheaf.stalk y₁) P.primeCompl (S := T.Y.presheaf.stalk T.y)
      (nonZeroDivisors (T.Y.presheaf.stalk T.y)) (FractionRing (T.Y.presheaf.stalk T.y))
      (fun x hx => hx.mem_nonZeroDivisors)
    have hinj : Function.Injective (algebraMap (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)) :=
      IsLocalization.injective (T.Y.presheaf.stalk T.y) (M := P.primeCompl)
        (le_nonZeroDivisors_of_noZeroDivisors fun h0 => h0 P.zero_mem)
    have heq : (nonZeroDivisors (T.Y.presheaf.stalk T.y)).comap
        (algebraMap (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)) = nonZeroDivisors (T.Y.presheaf.stalk y₁) :=
      le_antisymm (comap_nonZeroDivisors_le_of_injective hinj)
        (IsLocalization.nonZeroDivisors_le_comap (M := P.primeCompl) (S := T.Y.presheaf.stalk T.y))
    show IsLocalization (nonZeroDivisors (T.Y.presheaf.stalk y₁)) (FractionRing (T.Y.presheaf.stalk T.y))
    rw [← heq]; exact h1

  have hpt : (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (T.Y.presheaf.stalk T.y))
        (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f)).1 =
      (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (T.Y.presheaf.stalk T.y))
        (⟨T.Y.fromSpecStalk T.y, T.halg⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk T.y)))) T.f)).1 := by
    apply pullback.hom_ext
    · rw [NeronModelInfra.pointGenericFibre_coe_comp_fst, NeronModelInfra.pointGenericFibre_coe_comp_fst]
      show Spec.map (CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk y₁) (FractionRing (T.Y.presheaf.stalk T.y)))) ≫
          T.Y.fromSpecStalk y₁ =
        Spec.map (CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)))) ≫
          T.Y.fromSpecStalk T.y
      rw [IsScalarTower.algebraMap_eq (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)
          (FractionRing (T.Y.presheaf.stalk T.y)), CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      congr 1
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen
    · rw [NeronModelInfra.pointGenericFibre_coe_comp_snd, NeronModelInfra.pointGenericFibre_coe_comp_snd]
  letI algUF : Algebra Γ(XK, T.U) (FractionRing (T.Y.presheaf.stalk T.y)) := T.algebraU
  letI algKU : Algebra K Γ(XK, T.U) := gK.sectionsAlgebra T.U
  haveI towKUF : IsScalarTower K Γ(XK, T.U) (FractionRing (T.Y.presheaf.stalk T.y)) := T.isScalarTowerU
  have hx₁ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, T.U) (FractionRing (T.Y.presheaf.stalk T.y)))) ≫
      T.hU.fromSpec =
      (NeronModelInfra.schemeHomOverComp
        (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (T.Y.presheaf.stalk T.y))
          (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
        T.e).1 := by
    rw [T.hx]
    show (NeronModelInfra.pointGenericFibre _).1 ≫ T.e.1 = (NeronModelInfra.pointGenericFibre _).1 ≫ T.e.1
    rw [hpt]

  have hσ := h (FractionRing (T.Y.presheaf.stalk T.y)) T.U T.hU T.isScalarTowerU hx₁ T.ωU T.hωU

  obtain ⟨_, _, hlh, hidx⟩ := NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes
    T.f T.y T.hy T.hmax T.halg

  obtain ⟨hle, hiff⟩ :=
    NeronModelInfra.TopFormOrder.le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
      R K (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y))
      ϖ hϖ hidx.map_maximalIdeal d b' T.b m w _ hσ

  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)) := by
    haveI : IsLocalizedModule P.primeCompl
        (KaehlerDifferential.map R R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)) :=
      KaehlerDifferential.isLocalizedModule_map R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y) P.primeCompl
    have hbc := IsLocalizedModule.isBaseChange P.primeCompl (T.Y.presheaf.stalk T.y)
      (KaehlerDifferential.map R R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y))
    have heqv : ∀ x, KaehlerDifferential.mapBaseChange R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y) x =
        hbc.equiv x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s y => rw [KaehlerDifferential.mapBaseChange_tmul, IsBaseChange.equiv_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    have : ⇑(KaehlerDifferential.mapBaseChange R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)) = ⇑hbc.equiv :=
      funext heqv
    rw [this]; exact hbc.equiv.bijective
  have hord := hiff.mpr hbij

  obtain ⟨hρ0, -⟩ := NeronModelInfra.TopFormOrder.topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
    R K (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) d T.b
  obtain ⟨-, hordsmul⟩ := NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis
    R K (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) d T.b
  have hTa := hordsmul T.a T.ha0 hρ0
  rw [← T.ha] at hTa
  rw [hTa] at hord
  show m = TopFormOrder.addOrd (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) T.a
  exact hord.symm

end S_NeronModelInfra_ComponentReading_eq_n_of_forall_topFormMap_eq_mul_zpow_smul
end P2MW
export P2MW.S_NeronModelInfra_ComponentReading_eq_n_of_forall_topFormMap_eq_mul_zpow_smul (solution)
