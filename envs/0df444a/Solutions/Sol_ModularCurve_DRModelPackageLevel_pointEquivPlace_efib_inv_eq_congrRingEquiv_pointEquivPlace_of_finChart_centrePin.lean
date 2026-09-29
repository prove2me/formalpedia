-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/17937355-41be-5fb1-9ce6-f9f0404014ab

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_AlgebraicCurve_CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_AlgebraicCurve_CurveModel_infinite_place
import Theorems.Thm_ModularCurve_IgusaScheme_qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

section E3

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin.AlgebraicGeometry"

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.germ_stalkClosedPointTo_Spec Spec.map_preimage IsOpenImmersion.lift Scheme.Hom Scheme.Hom.germ_stalkMap_apply Scheme.stalkClosedPointTo_comp Scheme.SpecMap_stalkSpecializes_fromSpecStalk LocallyOfFiniteType Spec IsIntegral Spec.map Scheme LocallyOfFiniteType.jacobsonSpace Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Hom.appIso_inv_app_apply genericPoint_eq_of_isOpenImmersion pointEquivClosedPoint Spec.preimage Scheme.SpecMap_stalkMap_fromSpecStalk Scheme.Hom.germ_stalkMap IsOpenImmersion.lift_fac Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

section FFMap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (θ : X ⟶ Y) [IsIso θ]

private theorem e3_genericPoint_specializes :
    θ.base (genericPoint X) ⤳ genericPoint Y := by
  rw [genericPoint_eq_of_isOpenImmersion θ]

private noncomputable def e3_ffMap : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (e3_genericPoint_specializes θ) ≫ θ.stalkMap (genericPoint X)

@[reassoc]
private theorem e3_SpecMap_ffMap_fromSpecStalk :
    Spec.map (e3_ffMap θ) ≫ Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ θ := by
  rw [e3_ffMap, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

private theorem e3_germ_ffMap (U : Y.Opens) (hU : genericPoint Y ∈ U) :
    Y.presheaf.germ U (genericPoint Y) hU ≫ e3_ffMap θ =
      θ.app U ≫ X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) := by
  rw [e3_ffMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem e3_ffMap_germ_apply (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    e3_ffMap θ (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) (θ.app U s) := by
  rw [← CommRingCat.comp_apply, e3_germ_ffMap]; rfl

private theorem e3_ffMap_germ_of_eq {Z : Scheme.{u}} (g₂ : Y ⟶ Z) (g₁ : X ⟶ Z) (e : g₁ = θ ≫ g₂)
    (U : Z.Opens) (h₂ : genericPoint Y ∈ g₂ ⁻¹ᵁ U) (h₁ : genericPoint X ∈ g₁ ⁻¹ᵁ U) (s : Γ(Z, U)) :
    e3_ffMap θ (Y.presheaf.germ (g₂ ⁻¹ᵁ U) (genericPoint Y) h₂ (g₂.app U s)) =
      X.presheaf.germ (g₁ ⁻¹ᵁ U) (genericPoint X) h₁ (g₁.app U s) := by
  subst e
  rw [e3_ffMap_germ_apply]
  rfl

end FFMap

section ChartValue

variable {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}

private theorem e3_stalkClosedPointTo_germ_appIso_inv (ι : Y ⟶ X) [IsOpenImmersion ι] (l : Spec R ⟶ Y)
    (w : Γ(Y, ⊤)) (h : (l ≫ ι).base (IsLocalRing.closedPoint R) ∈ ι ''ᵁ ⊤) :
    Scheme.stalkClosedPointTo (l ≫ ι) (X.presheaf.germ (ι ''ᵁ ⊤) _ h ((ι.appIso ⊤).inv w)) =
      Scheme.stalkClosedPointTo l (Y.presheaf.germ ⊤ _ trivial w) := by
  rw [Scheme.stalkClosedPointTo_comp]
  show Scheme.stalkClosedPointTo l (ι.stalkMap (l.base (IsLocalRing.closedPoint R))
    (X.presheaf.germ (ι ''ᵁ ⊤) (ι.base (l.base (IsLocalRing.closedPoint R))) h ((ι.appIso ⊤).inv w))) = _
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply]

private theorem e3_stalkClosedPointTo_SpecMap_germ {A : CommRingCat.{u}} (φ : A ⟶ R) (b : A) :
    Scheme.stalkClosedPointTo (Spec.map φ) ((Spec A).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso A).inv b)) =
      φ b := by
  rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]

end ChartValue

end AlgebraicGeometry

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel Place Place.coe_algebraMap Place.ResidueField HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.hasPrincipalDivisors Place.congrRingEquiv CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "placeEquiv pointEquivPlace toBase C ffEquiv ffEquiv_algebraMap smooth X₀ centre pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo infinite_place"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

variable {K : Type u} [Field K] {L₁ : Type v} [Field L₁] [Algebra K L₁] {L₂ : Type v} [Field L₂] [Algebra K L₂]
  (M₁ : CurveModel K L₁) (M₂ : CurveModel K L₂) (θ : M₁.C ⟶ M₂.C) [IsIso θ]

private noncomputable def e3_ffPull : L₂ →+* L₁ :=
  M₁.ffEquiv.symm.toRingHom.comp ((e3_ffMap θ).hom.comp M₂.ffEquiv.toRingHom)

private theorem e3_ffPull_apply (f : L₂) : e3_ffPull M₁ M₂ θ f = M₁.ffEquiv.symm (e3_ffMap θ (M₂.ffEquiv f)) := rfl

private theorem e3_ffMap_baseToFunctionField (hθ : θ ≫ M₂.toBase = M₁.toBase) (a : K) :
    e3_ffMap θ (baseToFunctionField M₂.toBase a) = baseToFunctionField M₁.toBase a := by
  simp only [baseToFunctionField, RingHom.comp_apply]
  erw [e3_ffMap_germ_apply θ ⊤ trivial]
  rw [← hθ]
  rfl

private theorem e3_ffPull_algebraMap (hθ : θ ≫ M₂.toBase = M₁.toBase) (a : K) :
    e3_ffPull M₁ M₂ θ (algebraMap K L₂ a) = algebraMap K L₁ a := by
  rw [e3_ffPull_apply, M₂.ffEquiv_algebraMap, e3_ffMap_baseToFunctionField M₁ M₂ θ hθ,
    ← M₁.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]

private theorem e3_fromSpecStalk_comp_eq_of_ffPull_eq (φ : L₁ ≃+* L₂)
    (hΦ : ∀ f, e3_ffPull M₁ M₂ θ f = φ.symm f) :
    M₁.C.fromSpecStalk (genericPoint M₁.C) ≫ θ =
      Spec.map (CommRingCat.ofHom
        (M₁.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M₂.ffEquiv.symm.toRingHom))) ≫
        M₂.C.fromSpecStalk (genericPoint M₂.C) := by
  rw [← e3_SpecMap_ffMap_fromSpecStalk θ]
  congr 2
  ext z
  obtain ⟨w, rfl⟩ := M₂.ffEquiv.surjective z
  have h := hΦ w
  rw [e3_ffPull_apply, RingEquiv.symm_apply_eq] at h
  rw [h]
  simp

end AlgebraicCurve.CurveModel

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel Place Place.coe_algebraMap Place.ResidueField HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.hasPrincipalDivisors Place.congrRingEquiv CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "placeEquiv pointEquivPlace toBase C ffEquiv ffEquiv_algebraMap smooth X₀ centre pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo infinite_place"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

variable {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)

private theorem _root_.AlgebraicCurve.CurveModel.e3_genericPoint_not_mem_closedPoints : genericPoint M.C ∉ closedPoints M.C := by
  intro h
  haveI : Infinite (Place K L) := M.infinite_place
  have h1 : closure ({genericPoint M.C} : Set M.C) = {genericPoint M.C} :=
    (mem_closedPoints_iff.mp h).closure_eq
  rw [genericPoint_closure] at h1
  have hsub : closedPoints M.C ⊆ {genericPoint M.C} := fun x _ => by rw [← h1]; trivial
  have hfin : (closedPoints M.C).Finite := (Set.finite_singleton _).subset hsub
  haveI := hfin.to_subtype
  exact (Infinite.of_injective _ M.placeEquiv.symm.injective : Infinite (closedPoints M.C)).false

p2m_export "AlgebraicCurve.CurveModel" "e3_genericPoint_not_mem_closedPoints"

private theorem _root_.AlgebraicCurve.CurveModel.e3_pointEquivPlace_symm_closedPoint (x : closedPoints M.C) :
    M.pointEquivPlace ((pointEquivClosedPoint M.toBase).symm x) = M.placeEquiv x := by
  rw [pointEquivPlace, Equiv.trans_apply, Equiv.apply_symm_apply]

p2m_export "AlgebraicCurve.CurveModel" "e3_pointEquivPlace_symm_closedPoint"

private theorem _root_.AlgebraicCurve.CurveModel.e3_eq_zero_of_forall_mem_nonunits [HasPrincipalDivisors K L] (V : M.C.Opens)
    (hV : (V : Set M.C).Nonempty) (f : L)
    (hf : ∀ y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      y.1.base (IsLocalRing.closedPoint K) ∈ V → f ∈ (M.pointEquivPlace y).toValuationSubring.nonunits) :
    f = 0 := by
  by_contra hf0
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  let Z : Set M.C := ⋃ v ∈ D.support, {(M.placeEquiv.symm v).1}
  have hZ : IsClosed Z := isClosed_biUnion_finset fun v _ => (M.placeEquiv.symm v).2
  have hgen : genericPoint M.C ∈ (V : Set M.C) \ Z := by
    refine ⟨((genericPoint_spec M.C).mem_open_set_iff V.isOpen).mpr (by simpa using hV), fun hz => ?_⟩
    simp only [Z, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨v, -, hv⟩ := hz
    exact M.e3_genericPoint_not_mem_closedPoints (hv ▸ (M.placeEquiv.symm v).2)
  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨x, ⟨hxV, hxZ⟩, hxc⟩ :=
    nonempty_inter_closedPoints ⟨_, hgen⟩ (V.isOpen.sdiff hZ).isLocallyClosed
  let y := (pointEquivClosedPoint M.toBase).symm ⟨x, hxc⟩
  have hy0 : y.1.base (IsLocalRing.closedPoint K) = x := by simp [y]
  have hmem := hf y (by rw [hy0]; exact hxV)
  have hplace : M.pointEquivPlace y = M.placeEquiv ⟨x, hxc⟩ := M.e3_pointEquivPlace_symm_closedPoint ⟨x, hxc⟩
  obtain ⟨hfO, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hmem
  have hlt := ((M.pointEquivPlace y).mem_maximalIdeal_iff_adicValuation_lt_one ⟨f, hfO⟩).mp hmax
  have hord : (M.pointEquivPlace y).ord f ≠ 0 := fun h0 => by
    rw [((M.pointEquivPlace y).ord_eq_zero_iff_adicValuation_eq_one hf0).mp h0] at hlt
    exact lt_irrefl _ hlt
  apply hxZ
  simp only [Z, Set.mem_iUnion, Set.mem_singleton_iff]
  refine ⟨M.pointEquivPlace y, Finsupp.mem_support_iff.mpr (by rw [hD]; exact hord), ?_⟩
  rw [hplace, Equiv.symm_apply_apply]

p2m_export "AlgebraicCurve.CurveModel" "e3_eq_zero_of_forall_mem_nonunits"

private theorem _root_.AlgebraicCurve.CurveModel.e3_sub_algebraMap_mem_maximalIdeal_of_stalkClosedPointTo_eq
    (y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (V : M.C.Opens)
    (hy : y.1.base (IsLocalRing.closedPoint K) ∈ V) (hVgen : genericPoint M.C ∈ V) (t : Γ(M.C, V)) (c : K)
    (hval : Scheme.stalkClosedPointTo y.1 (M.C.presheaf.germ V _ hy t) = c) :
    ∃ h : M.ffEquiv.symm (M.C.presheaf.germ V (genericPoint M.C) hVgen t) ∈ (M.pointEquivPlace y).toValuationSubring,
      (⟨_, h⟩ : (M.pointEquivPlace y).toValuationSubring) -
          algebraMap K (M.pointEquivPlace y).toValuationSubring c ∈
        IsLocalRing.maximalIdeal (M.pointEquivPlace y).toValuationSubring := by
  have key := M.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo y (M.C.presheaf.germ V _ hy t)
  have halg : algebraMap (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint K))) M.C.functionField
      (M.C.presheaf.germ V _ hy t) = M.C.presheaf.germ V (genericPoint M.C) hVgen t := by
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rw [halg, hval] at key
  obtain ⟨h, hres, -⟩ := key
  refine ⟨h, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, IsScalarTower.algebraMap_apply K (M.pointEquivPlace y).toValuationSubring (Place.ResidueField _) c,
    IsLocalRing.ResidueField.algebraMap_eq, sub_self]

p2m_export "AlgebraicCurve.CurveModel" "e3_sub_algebraMap_mem_maximalIdeal_of_stalkClosedPointTo_eq"
omit [IsAlgClosed K] in

private theorem e3_sub_mem_nonunits_of_pins (v : Place K L) (F G : L) (c : K)
    (hF : ∃ h : F ∈ v.toValuationSubring,
      (⟨F, h⟩ : v.toValuationSubring) - algebraMap K v.toValuationSubring c ∈ IsLocalRing.maximalIdeal v.toValuationSubring)
    (hG : G ∈ v.toValuationSubring ∧ G - algebraMap K L c ∈ v.toValuationSubring.nonunits) :
    F - G ∈ v.toValuationSubring.nonunits := by
  obtain ⟨hFm, hFmax⟩ := hF
  obtain ⟨hGm', hGmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hG.2
  refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨sub_mem hFm hG.1, ?_⟩
  have : (⟨F - G, sub_mem hFm hG.1⟩ : v.toValuationSubring) =
      (⟨F, hFm⟩ - algebraMap K v.toValuationSubring c) - ⟨G - algebraMap K L c, hGm'⟩ := by
    ext
    simp [Place.coe_algebraMap]
  rw [this]
  exact Ideal.sub_mem _ hFmax hGmax

end AlgebraicCurve.CurveModel

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.germ_stalkClosedPointTo_Spec Spec.map_preimage IsOpenImmersion.lift Scheme.Hom Scheme.Hom.germ_stalkMap_apply Scheme.stalkClosedPointTo_comp Scheme.SpecMap_stalkSpecializes_fromSpecStalk LocallyOfFiniteType Spec IsIntegral Spec.map Scheme LocallyOfFiniteType.jacobsonSpace Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Hom.appIso_inv_app_apply genericPoint_eq_of_isOpenImmersion pointEquivClosedPoint Spec.preimage Scheme.SpecMap_stalkMap_fromSpecStalk Scheme.Hom.germ_stalkMap IsOpenImmersion.lift_fac Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

private theorem e3_exists_eq_SpecMap_comp {K : Type u} [Field K] {X : Scheme.{u}} {A : CommRingCat.{u}}
    (f : Spec (CommRingCat.of K) ⟶ X) (ι : Spec A ⟶ X) [IsOpenImmersion ι]
    (h : f.base (IsLocalRing.closedPoint K) ∈ ι ''ᵁ ⊤) :
    ∃ β : A →+* K, f = Spec.map (CommRingCat.ofHom β) ≫ ι := by
  have H : Set.range f.base ⊆ Set.range ι.base := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    obtain ⟨z, -, hz⟩ := h
    exact ⟨z, hz⟩
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ι f H)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

private theorem e3_stalkClosedPointTo_germ_app_chart {K : Type u} [Field K] {X Z : Scheme.{u}} {A : CommRingCat.{u}}
    (g : X ⟶ Z) (ι : Spec A ⟶ Z) [IsOpenImmersion ι] (y : Spec (CommRingCat.of K) ⟶ X) (β : A ⟶ CommRingCat.of K)
    (e : y ≫ g = Spec.map β ≫ ι) (b : A) (hy : (y ≫ g).base (IsLocalRing.closedPoint K) ∈ ι ''ᵁ ⊤) :
    Scheme.stalkClosedPointTo y (X.presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) (y.base (IsLocalRing.closedPoint K)) hy
      (g.app _ ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)))) = β b := by
  have key : ∀ (f : Spec (CommRingCat.of K) ⟶ Z) (hf : f.base (IsLocalRing.closedPoint K) ∈ ι ''ᵁ ⊤),
      f = Spec.map β ≫ ι →
      Scheme.stalkClosedPointTo f (Z.presheaf.germ _ _ hf ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b))) = β b := by
    rintro f hf rfl
    rw [e3_stalkClosedPointTo_germ_appIso_inv, e3_stalkClosedPointTo_SpecMap_germ]
  rw [← Scheme.Hom.germ_stalkMap_apply g (ι ''ᵁ ⊤) (y.base (IsLocalRing.closedPoint K)) hy]
  have h2 : Scheme.stalkClosedPointTo y (g.stalkMap _ (Z.presheaf.germ (ι ''ᵁ ⊤) _ hy
      ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)))) =
    Scheme.stalkClosedPointTo (y ≫ g) (Z.presheaf.germ (ι ''ᵁ ⊤) _ hy ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b))) := by
    rw [Scheme.stalkClosedPointTo_comp]; rfl
  exact h2.trans (key _ hy e)

end AlgebraicGeometry

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRModelPackageLevel IgusaScheme IgusaScheme.ιFin qExpand jq modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jGeomGen jNGeomGen jqModC jqNModC modularFunctionFieldC modularFunctionFieldFullC modularFunctionFieldC_le_full isCurveOver_modularFunctionFieldFullC"
p2m_open "ModularCurve"

p2m_open "ModularCurve.IgusaScheme ModularCurve.CharPModel AlgebraicCurve P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin.AlgebraicCurve IsLocalRing"

private noncomputable abbrev e3_sec (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (b : ↥(chartAlgFin N₀ q)) :
    Γ(IgusaScheme N₀ q, (ιFin N₀ q) ''ᵁ ⊤) :=
  ((ιFin N₀ q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin N₀ q))).inv b)

private noncomputable def e3_jNChartFin (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] : ↥(chartAlgFin N₀ q) :=
  ⟨⟨qExpand ℚ N₀ jq, jqd_mem_full N₀ (dvd_refl N₀)⟩,
    (qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg N₀ q N₀ (dvd_refl N₀)).2.1⟩

private theorem e3_coe_jNChartFin (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] :
    ((e3_jNChartFin N₀ q : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq := rfl

section FibreModelPins

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  {k : Type*} [Field k] [CharP k q] (red : ↥A →+* k) (fm : FibreModel N₀ A q k red)

private theorem e3_piFin_jChartFin
    (hfin : ∀ b : chartAlgFin N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin) :
    fm.piFin ⟨_, hfin (jChartFin N₀ q)⟩ = jGeomGen k N₀ := by
  have h : (⟨_, hfin (jChartFin N₀ q)⟩ : ↥fm.BFin) = ⟨jBar N₀, fm.jBar_mem⟩ := Subtype.ext rfl
  rw [h, fm.piFin_j]
  rfl

private theorem e3_piFin_jNChartFin
    (hfin : ∀ b : chartAlgFin N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin) :
    fm.piFin ⟨_, hfin (e3_jNChartFin N₀ q)⟩ = jNGeomGen k N₀ := by
  have h : (⟨_, hfin (e3_jNChartFin N₀ q)⟩ : ↥fm.BFin) = ⟨jNBar N₀, fm.jNBar_mem⟩ := Subtype.ext rfl
  rw [h, fm.piFin_jN]
  rfl

end FibreModelPins

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem e3_ffEquiv_symm_germ_chart_eq_inclusion_piFin (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)]
    (toκ : ↥(GaloisRep.ratLocalizedAt q) →+* ResidueField ↥A)
    (Ms : CurveModel (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀))
    (es : Ms.C ⟶ pullback (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
    (fm : FibreModel N₀ A q (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (hfin : ∀ b : chartAlgFin N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin)
    (hspFin : ∀ (y : {q' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q' ≫ Ms.toBase = 𝟙 _})
        (β : ↥(chartAlgFin N₀ q) →+* ResidueField ↥A),
        y.1 ≫ es ≫ pullback.fst (igusaTo N₀ q) _ =
          Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιFin N₀ q →
        ∀ b : ↥(chartAlgFin N₀ q),
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N₀) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀)) ∈
            (Ms.pointEquivPlace y).toValuationSubring ∧
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N₀) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀)) -
              algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) (β b) ∈
            (Ms.pointEquivPlace y).toValuationSubring.nonunits)
    (hgen : genericPoint Ms.C ∈
      (es ≫ pullback.fst (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((ιFin N₀ q) ''ᵁ ⊤))
    (b : ↥(chartAlgFin N₀ q)) :
    Ms.ffEquiv.symm (Ms.C.presheaf.germ _ (genericPoint Ms.C) hgen
      ((es ≫ pullback.fst (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app _ (e3_sec N₀ q b))) =
      IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N₀) (fm.piFin ⟨_, hfin b⟩) := by
  haveI : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
    isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) N₀
  haveI : HasPrincipalDivisors (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
    IsCurveOver.hasPrincipalDivisors (K := ResidueField ↥A) (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀))
  rw [← sub_eq_zero]
  refine Ms.e3_eq_zero_of_forall_mem_nonunits _ ⟨_, hgen⟩ _ fun y hy => ?_
  obtain ⟨β, hβ⟩ := e3_exists_eq_SpecMap_comp
    (y.1 ≫ es ≫ pullback.fst (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ))) (ιFin N₀ q) hy
  have hsp := hspFin y β hβ b
  have hval := e3_stalkClosedPointTo_germ_app_chart
    (es ≫ pullback.fst (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ))) (ιFin N₀ q) y.1 (CommRingCat.ofHom β) hβ
    b hy
  exact AlgebraicCurve.CurveModel.e3_sub_mem_nonunits_of_pins (Ms.pointEquivPlace y) _ _ (β b)
    (Ms.e3_sub_algebraMap_mem_maximalIdeal_of_stalkClosedPointTo_eq y _ hy hgen _ (β b) hval) hsp

private theorem e3_forall_eq_equivOfEq_symm_of_fixes_generators (κ : Type*) [Field κ] (N : ℕ) [NeZero N]
    (E : IntermediateField κ (LaurentSeries κ)) (hCF : modularFunctionFieldC κ N = E)
    (Φ : ↥E →+* ↥(modularFunctionFieldC κ N))
    (hΦK : ∀ a, Φ (algebraMap κ ↥E a) = algebraMap κ _ a)
    (hj : Φ (IntermediateField.equivOfEq hCF (jGeomGen κ N)) = jGeomGen κ N)
    (hjN : Φ (IntermediateField.equivOfEq hCF (jNGeomGen κ N)) = jNGeomGen κ N) :
    ∀ f, Φ f = (IntermediateField.equivOfEq hCF).toRingEquiv.symm f := by
  subst hCF
  let ψ : ↥(modularFunctionFieldC κ N) →ₐ[κ] ↥(modularFunctionFieldC κ N) :=
    { Φ.comp (IntermediateField.equivOfEq rfl).toRingEquiv.toRingHom with
      commutes' := fun a => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
          RingHom.coe_comp, Function.comp_apply]
        exact (congrArg Φ ((IntermediateField.equivOfEq rfl).commutes a)).trans (hΦK a) }
  have hψ : ψ = AlgHom.id κ _ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin (F := κ)
      (s := ({jqModC κ, jqNModC κ N} : Set (LaurentSeries κ))) rfl ?_
    rintro x (rfl | rfl)
    · exact hj
    · exact hjN
  intro f
  have h2 := AlgHom.congr_fun hψ ((IntermediateField.equivOfEq rfl).toRingEquiv.symm f)
  simpa [ψ] using h2

end ModularCurve

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin.AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin.ModularCurve ModularCurve.CharPModel AlgebraicCurve P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin.AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme"

open scoped TensorProduct

open ModularCurve.DRLevel

noncomputable section

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    (toκ : ↥(GaloisRep.ratLocalizedAt q) →+* ResidueField ↥A)
    (Ms : CurveModel (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀))
    (es : Ms.C ⟶ pullback (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ))) [IsIso es]
    (hes : es ≫ pullback.snd (igusaTo N₀ q) _ = Ms.toBase)
    (fm : FibreModel N₀ A q (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (hfin : ∀ b : chartAlgFin N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin)
    (hspFin : ∀ (y : {q' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q' ≫ Ms.toBase = 𝟙 _})
        (β : ↥(chartAlgFin N₀ q) →+* ResidueField ↥A),
        y.1 ≫ es ≫ pullback.fst (igusaTo N₀ q) _ =
          Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιFin N₀ q →
        ∀ b : ↥(chartAlgFin N₀ q),
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N₀) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀)) ∈
            (Ms.pointEquivPlace y).toValuationSubring ∧
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N₀) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀)) -
              algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) (β b) ∈
            (Ms.pointEquivPlace y).toValuationSubring.nonunits)
    (hCF : modularFunctionFieldC (ResidueField ↥A) N₀ = modularFunctionFieldFullC (ResidueField ↥A) N₀) :
    ∀ y' : {q' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔓.Mfib (ResidueField ↥A) toκ).C //
        q' ≫ (𝔓.Mfib (ResidueField ↥A) toκ).toBase = 𝟙 _},
      Ms.pointEquivPlace ⟨y'.1 ≫ 𝔓.efib (ResidueField ↥A) toκ ≫ inv es, by
          haveI := 𝔓.efib_iso (ResidueField ↥A) toκ
          rw [Category.assoc, Category.assoc, ← hes, IsIso.inv_hom_id_assoc, 𝔓.hefib]
          exact y'.2⟩ =
        AlgebraicCurve.Place.congrRingEquiv
          (e := (IntermediateField.equivOfEq hCF).toRingEquiv)
          (he := fun a => (IntermediateField.equivOfEq hCF).commutes a)
          ((𝔓.Mfib (ResidueField ↥A) toκ).pointEquivPlace y') := by
  intro y'
  haveI := 𝔓.efib_iso (ResidueField ↥A) toκ
  let θ := 𝔓.efib (ResidueField ↥A) toκ ≫ inv es
  have hθ : θ ≫ Ms.toBase = (𝔓.Mfib (ResidueField ↥A) toκ).toBase := by
    simp only [θ, Category.assoc]
    rw [← hes, IsIso.inv_hom_id_assoc, 𝔓.hefib]
  have e : 𝔓.efib (ResidueField ↥A) toκ ≫ pullback.fst (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) =
      θ ≫ es ≫ pullback.fst (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ)) := by
    simp only [θ, Category.assoc, IsIso.inv_hom_id_assoc]

  have hne1 : genericPoint (𝔓.Mfib (ResidueField ↥A) toκ).C ∈
      (𝔓.efib (ResidueField ↥A) toκ ≫ pullback.fst (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
        ((ιFin N₀ q) ''ᵁ ⊤) := by
    obtain ⟨z⟩ := 𝔓.Mfib_chart_nonempty (ResidueField ↥A) toκ
    exact ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨z.1, trivial, z.2⟩
  have hgen : genericPoint Ms.C ∈
      (es ≫ pullback.fst (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((ιFin N₀ q) ''ᵁ ⊤) := by
    have h' := hne1
    rw [e] at h'
    have h'' : θ.base (genericPoint (𝔓.Mfib (ResidueField ↥A) toκ).C) ∈
        (es ≫ pullback.fst (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((ιFin N₀ q) ''ᵁ ⊤) := h'
    rwa [genericPoint_eq_of_isOpenImmersion] at h''
  have hS := e3_ffEquiv_symm_germ_chart_eq_inclusion_piFin N₀ q A toκ Ms es fm hfin hspFin hgen

  have hΦ : ∀ f, AlgebraicCurve.CurveModel.e3_ffPull (𝔓.Mfib (ResidueField ↥A) toκ) Ms θ f =
      (IntermediateField.equivOfEq hCF).toRingEquiv.symm f := by
    refine e3_forall_eq_equivOfEq_symm_of_fixes_generators (ResidueField ↥A) N₀ _ hCF _
      (fun a => AlgebraicCurve.CurveModel.e3_ffPull_algebraMap _ _ θ hθ a) ?_ ?_
    · rw [AlgebraicCurve.CurveModel.e3_ffPull_apply,
        show IntermediateField.equivOfEq hCF (jGeomGen (ResidueField ↥A) N₀) =
          IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N₀)
            (fm.piFin ⟨_, hfin (jChartFin N₀ q)⟩) from by rw [e3_piFin_jChartFin]; rfl,
        ← hS (jChartFin N₀ q), RingEquiv.apply_symm_apply,
        e3_ffMap_germ_of_eq θ _ _ e _ hgen hne1]
      exact (𝔓.Mfib_pin (ResidueField ↥A) toκ (jChartFin N₀ q)).1 rfl
    · rw [AlgebraicCurve.CurveModel.e3_ffPull_apply,
        show IntermediateField.equivOfEq hCF (jNGeomGen (ResidueField ↥A) N₀) =
          IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N₀)
            (fm.piFin ⟨_, hfin (e3_jNChartFin N₀ q)⟩) from by rw [e3_piFin_jNChartFin]; rfl,
        ← hS (e3_jNChartFin N₀ q), RingEquiv.apply_symm_apply,
        e3_ffMap_germ_of_eq θ _ _ e _ hgen hne1]
      exact (𝔓.Mfib_pin (ResidueField ↥A) toκ (e3_jNChartFin N₀ q)).2 rfl
  exact AlgebraicCurve.CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
    (𝔓.Mfib (ResidueField ↥A) toκ) Ms (IntermediateField.equivOfEq hCF).toRingEquiv
    (fun a => (IntermediateField.equivOfEq hCF).commutes a) θ hθ
    (AlgebraicCurve.CurveModel.e3_fromSpecStalk_comp_eq_of_ffPull_eq _ _ θ _ hΦ) y'

end

end E3

end S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin (solution)
