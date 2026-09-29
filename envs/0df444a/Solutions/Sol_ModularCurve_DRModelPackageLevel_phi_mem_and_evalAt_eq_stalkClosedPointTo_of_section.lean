-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.phi_mem_and_evalAt_eq_stalkClosedPointTo_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c398e8fe-7b53-59de-b05a-b6dca66b5d28

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
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
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_AlgebraicGeometry_exists_isUnit_mul_eq_mem_closure_of_stalk_pullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_phi_mem_and_evalAt_eq_stalkClosedPointTo_of_section

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace EvalMatchLevel

universe u

private theorem stalkClosedPointTo_germ_const {O : Type u} [CommRing O] [IsLocalRing O]
    {Y : Scheme.{u}} (u : Y ⟶ Spec (CommRingCat.of O)) (t : Spec (CommRingCat.of O) ⟶ Y) (ht : t ≫ u = 𝟙 _) (a : O) :
    (Scheme.stalkClosedPointTo t).hom ((Y.presheaf.germ ⊤ (t.base (IsLocalRing.closedPoint O)) trivial).hom
      (u.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a))) = a := by
  have hsec : ∀ y : Γ(Spec (CommRingCat.of O), ⊤), (t.app ⊤).hom (u.appTop.hom y) = y := by
    intro y
    have h := Scheme.Hom.comp_appTop t u
    rw [ht] at h
    have h2 := congrArg (fun φ : Γ(Spec (CommRingCat.of O), ⊤) ⟶ Γ(Spec (CommRingCat.of O), ⊤) => φ.hom y) h
    simp at h2
    exact h2.symm
  show ((Y.presheaf.germ ⊤ (t.base (IsLocalRing.closedPoint O)) trivial) ≫
    Scheme.stalkClosedPointTo t).hom (u.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) = a
  rw [Scheme.germ_stalkClosedPointTo t ⊤ trivial]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, eqToIso.hom, hsec]
  try simp only [RingHom.id_apply]
  change ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom a = a
  rw [Iso.inv_hom_id]
  rfl

private theorem stalkClosedPointTo_comp_germ {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}
    (q : Spec R ⟶ X) (g : X ⟶ Y) (U : Y.Opens) (hU : (q ≫ g).base (IsLocalRing.closedPoint R) ∈ U) (f : Γ(Y, U)) :
    (Scheme.stalkClosedPointTo (q ≫ g)).hom ((Y.presheaf.germ U _ hU).hom f) =
      (Scheme.stalkClosedPointTo q).hom ((X.presheaf.germ (g ⁻¹ᵁ U) (q.base (IsLocalRing.closedPoint R)) hU).hom
        ((g.app U).hom f)) := by
  rw [Scheme.stalkClosedPointTo_comp]
  show ((Y.presheaf.germ U _ hU ≫ g.stalkMap _) ≫ Scheme.stalkClosedPointTo q).hom f = _
  erw [Scheme.Hom.germ_stalkMap g U (q.base (IsLocalRing.closedPoint R)) hU]
  rfl

private theorem map_stalkClosedPointTo_germ {O K' : Type u} [CommRing O] [IsLocalRing O] [CommRing K'] [IsLocalRing K']
    (φ : CommRingCat.of O ⟶ CommRingCat.of K') {Y : Scheme.{u}} (t : Spec (CommRingCat.of O) ⟶ Y) (U : Y.Opens)
    (hU : t.base (IsLocalRing.closedPoint O) ∈ U)
    (hU' : (Spec.map φ ≫ t).base (IsLocalRing.closedPoint K') ∈ U) (f : Γ(Y, U)) :
    φ.hom ((Scheme.stalkClosedPointTo t).hom ((Y.presheaf.germ U _ hU).hom f)) =
      (Scheme.stalkClosedPointTo (Spec.map φ ≫ t)).hom ((Y.presheaf.germ U _ hU').hom f) := by

  have key : ∀ {S : Type u} [CommRing S] [IsLocalRing S] (r : Spec (CommRingCat.of S) ⟶ Y)
      (hr : r.base (IsLocalRing.closedPoint S) ∈ U),
      (Scheme.stalkClosedPointTo r).hom ((Y.presheaf.germ U _ hr).hom f) =
        (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((r.appLE U ⊤
          (by rw [Scheme.preimage_eq_top_of_closedPoint_mem r hr])).hom f) := by
    intro S _ _ r hr
    have h := congrArg (fun ψ => ψ.hom f) (Scheme.germ_stalkClosedPointTo r U hr)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
    rw [h]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    congr 1
  rw [key t hU, key (Spec.map φ ≫ t) hU']
  have hcomp : (Spec.map φ ≫ t).appLE U ⊤ (by rw [Scheme.preimage_eq_top_of_closedPoint_mem _ hU']) =
      t.appLE U ⊤ (by rw [Scheme.preimage_eq_top_of_closedPoint_mem t hU]) ≫ (Spec.map φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [hcomp]
  have hnat := congrArg (fun ψ => ψ.hom ((t.appLE U ⊤ (by rw [Scheme.preimage_eq_top_of_closedPoint_mem t hU])).hom f))
    (Scheme.ΓSpecIso_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hnat
  simpa using hnat.symm

private theorem algebraMap_germ_eq_germToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U)
    [Nonempty U] (f : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ U x hx).hom f) = (X.germToFunctionField U).hom f := by
  change ((X.presheaf.germ U x hx) ≫ X.presheaf.stalkSpecializes _).hom f = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

private theorem isUnit_valuationSubring_mk_iff {F : Type*} [Field F] (A : ValuationSubring F) (g : F) (hg : g ∈ A) :
    IsUnit (⟨g, hg⟩ : A) ↔ g ≠ 0 ∧ g⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu⟩
    have hmul : g * ((u⁻¹ : Aˣ) : A).1 = 1 := by
      have := congrArg (fun w : A => (w : F)) u.mul_inv
      simpa [hu] using this
    have hg0 : g ≠ 0 := fun h => by simp [h] at hmul
    refine ⟨hg0, ?_⟩
    have : g⁻¹ = ((u⁻¹ : Aˣ) : A).1 := by
      rw [inv_eq_of_mul_eq_one_right hmul]
    rw [this]; exact ((u⁻¹ : Aˣ) : A).2
  · rintro ⟨hg0, hinv⟩
    exact ⟨⟨⟨g, hg⟩, ⟨g⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hg0), Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩

private theorem residue_eq_algebraMap_iff {K S : Type*} [Field K] [CommRing S] [IsLocalRing S] [Algebra K S] (x : S) (c : K) :
    IsLocalRing.residue S x = algebraMap K (IsLocalRing.ResidueField S) c ↔ ¬ IsUnit (x - algebraMap K S c) := by
  rw [show algebraMap K (IsLocalRing.ResidueField S) c = IsLocalRing.residue S (algebraMap K S c) from rfl,
    ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

end EvalMatchLevel

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution

    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

    (𝔓 : DRModelPackageLevel N₀ q hqN)

    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (x : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x) _
        (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) a))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((φ ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
          (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))

    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))
    (t : Spec (CommRingCat.of O) ⟶ (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))) (ht₀ : t ≫ (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) = 𝟙 _)
    (ht : Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ t ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) =
      ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _)
    (hx : t.base (IsLocalRing.closedPoint O) = x)
    (hxfin : x ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
    (s : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk (t.base (IsLocalRing.closedPoint O))) :
    φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkCongr (.of_eq hx)).hom.hom s)) ∈ V.toValuationSubring ∧
    V.evalAt (φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkCongr (.of_eq hx)).hom.hom s))) =
      ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) (Scheme.stalkClosedPointTo t s) := by
  classical
  subst hx
  set jO : O →+* AlgebraicClosure ℚ := (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)) with hjO
  haveI := 𝔓.Meta_chart_nonempty
  letI : Algebra (DRLevel.R q) O := ρO.toAlgebra
  have hsc : ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.stalkCongr (Inseparable.of_eq (rfl : t.base (IsLocalRing.closedPoint O) =
      t.base (IsLocalRing.closedPoint O)))).hom.hom s = s := by simp
  rw [hsc]

  set y := 𝔓.Meta.pointEquivPlace.symm V with hy
  have hyV : 𝔓.Meta.pointEquivPlace y = V := Equiv.apply_symm_apply _ _
  set jK : CommRingCat.of O ⟶ CommRingCat.of (AlgebraicClosure ℚ) := CommRingCat.ofHom (jO) with hjK
  set z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) := Spec.map jK ≫ t with hz
  have hzt : z ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) = y.1 ≫ 𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))))) := by rw [hz, Category.assoc]; exact ht

  have hgenU : z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) := by
    have hsp : (Spec.map jK).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ IsLocalRing.closedPoint O :=
      IsLocalRing.specializes_closedPoint _
    have hsp' : z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ t.base (IsLocalRing.closedPoint O) := by
      rw [hz, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
      exact hsp.map t.base.hom.continuous
    exact hsp'.mem_open ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).isOpen hxfin
  have hgenU' : (z ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO))))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) := hgenU
  have hyU' : (y.1 ≫ 𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) := by
    rw [← hzt]; exact hgenU'
  have hyU : y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ (𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) := hyU'

  let val : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.stalk (t.base (IsLocalRing.closedPoint O)) →+* AlgebraicClosure ℚ :=
    (jO).comp (Scheme.stalkClosedPointTo t).hom
  have hval : ∀ r, val r = jO ((Scheme.stalkClosedPointTo t).hom r) := fun r => rfl
  let rd : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.stalk (t.base (IsLocalRing.closedPoint O)) →+* ↥(modularFunctionFieldBar (N₀ * q)) :=
    φ.comp (algebraMap _ (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).functionField)
  have hrd : ∀ r, rd r = φ (algebraMap _ (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).functionField r) := fun r => rfl
  let Pr : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.stalk (t.base (IsLocalRing.closedPoint O)) → Prop := fun r =>
    ∃ h : rd r ∈ V.toValuationSubring,
      IsLocalRing.residue V.toValuationSubring ⟨rd r, h⟩ = algebraMap (AlgebraicClosure ℚ) V.ResidueField (val r)

  have hconst : ∀ c : AlgebraicClosure ℚ, ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) c ∈
      V.toValuationSubring, IsLocalRing.residue V.toValuationSubring ⟨_, h⟩ =
        algebraMap (AlgebraicClosure ℚ) V.ResidueField c := by
    intro c
    refine ⟨V.algebraMap_mem' c, ?_⟩
    have : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) c, V.algebraMap_mem' c⟩ :
        V.toValuationSubring) = algebraMap (AlgebraicClosure ℚ) V.toValuationSubring c := Subtype.ext rfl
    rw [this]
    rfl

  have Padd : ∀ r₁ r₂, Pr r₁ → Pr r₂ → Pr (r₁ + r₂) := by
    rintro r₁ r₂ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    refine ⟨by rw [map_add]; exact add_mem h₁ h₂, ?_⟩
    have : (⟨rd (r₁ + r₂), by rw [map_add]; exact add_mem h₁ h₂⟩ : V.toValuationSubring) = ⟨rd r₁, h₁⟩ + ⟨rd r₂, h₂⟩ :=
      Subtype.ext (map_add rd r₁ r₂)
    rw [this, map_add, e₁, e₂, map_add, map_add]
  have Pmul : ∀ r₁ r₂, Pr r₁ → Pr r₂ → Pr (r₁ * r₂) := by
    rintro r₁ r₂ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    refine ⟨by rw [map_mul]; exact mul_mem h₁ h₂, ?_⟩
    have : (⟨rd (r₁ * r₂), by rw [map_mul]; exact mul_mem h₁ h₂⟩ : V.toValuationSubring) = ⟨rd r₁, h₁⟩ * ⟨rd r₂, h₂⟩ :=
      Subtype.ext (map_mul rd r₁ r₂)
    rw [this, map_mul, e₁, e₂, map_mul, map_mul]
  have Pneg : ∀ r, Pr r → Pr (-r) := by
    rintro r ⟨h, e⟩
    refine ⟨by rw [map_neg]; exact neg_mem h, ?_⟩
    have : (⟨rd (-r), by rw [map_neg]; exact neg_mem h⟩ : V.toValuationSubring) = -⟨rd r, h⟩ :=
      Subtype.ext (map_neg rd r)
    rw [this, map_neg, e, map_neg, map_neg]
  have Pone : Pr 1 := by
    refine ⟨by rw [map_one]; exact one_mem _, ?_⟩
    have : (⟨rd 1, by rw [map_one]; exact one_mem _⟩ : V.toValuationSubring) = 1 := Subtype.ext (map_one rd)
    rw [this, map_one, map_one, map_one]
  have Pzero : Pr 0 := by
    refine ⟨by rw [map_zero]; exact zero_mem _, ?_⟩
    have : (⟨rd 0, by rw [map_zero]; exact zero_mem _⟩ : V.toValuationSubring) = 0 := Subtype.ext (map_zero rd)
    rw [this, map_zero, map_zero, map_zero]

  have Pconst : ∀ o : O, Pr (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ⊤ (t.base (IsLocalRing.closedPoint O)) trivial).hom
      (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) := by
    intro o
    obtain ⟨h, e⟩ := hconst (jO o)
    have hv : val (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ⊤ (t.base (IsLocalRing.closedPoint O)) trivial).hom
        (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) = jO o := by
      rw [hval, EvalMatchLevel.stalkClosedPointTo_germ_const (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) t ht₀ o]
    have hr : rd (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ⊤ (t.base (IsLocalRing.closedPoint O)) trivial).hom
        (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (jO o) := hφO o
    refine ⟨hr ▸ h, ?_⟩
    rw [hv, ← e]
    congr 1
    exact Subtype.ext hr

  have htransfer : ∀ (f f' : ↥(modularFunctionFieldBar (N₀ * q)))
      (hff : (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)))
      (c : AlgebraicClosure ℚ) (h' : f' ∈ V.toValuationSubring)
      (e' : IsLocalRing.residue V.toValuationSubring ⟨f', h'⟩ = algebraMap (AlgebraicClosure ℚ) _ c),
      ∃ h : f ∈ V.toValuationSubring,
        IsLocalRing.residue V.toValuationSubring ⟨f, h⟩ = algebraMap (AlgebraicClosure ℚ) V.ResidueField c := by
    intro f f' hff c h' e'
    obtain rfl : f = f' := Subtype.ext hff
    exact ⟨h', e'⟩

  have Pchart : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q), Pr (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (t.base (IsLocalRing.closedPoint O)) hxfin).hom
      (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) := by
    intro a

    have hread : rd (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (t.base (IsLocalRing.closedPoint O)) hxfin).hom (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) = φ ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) := by
      rw [hrd, EvalMatchLevel.algebraMap_germ_eq_germToFunctionField]
    have hff : ((rd (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (t.base (IsLocalRing.closedPoint O)) hxfin).hom (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull (N₀ * q))).2⟩ : ↥(modularFunctionFieldBar (N₀ * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hread]
      exact hφj a

    have hMηa : (⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull (N₀ * q))).2⟩ : ↥(modularFunctionFieldBar (N₀ * q))) = 𝔓.Meta.ffEquiv.symm (algebraMap _ 𝔓.Meta.C.functionField
        ((𝔓.Meta.C.presheaf.germ ((𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyU).hom (((𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))))) := by
      rw [EvalMatchLevel.algebraMap_germ_eq_germToFunctionField]
      apply Subtype.ext
      exact (𝔓.Meta_pin a).symm

    have hL1 := AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
      𝔓.Meta y ((𝔓.Meta.C.presheaf.germ ((𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyU).hom (((𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))))
    rw [← hMηa, hyV] at hL1
    obtain ⟨h1, hres1, -⟩ := hL1

    have hv1 : (Scheme.stalkClosedPointTo y.1).hom ((𝔓.Meta.C.presheaf.germ ((𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
        (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyU).hom (((𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) =
        (Scheme.stalkClosedPointTo (y.1 ≫ 𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))))))).hom (((DRLevel.X N₀ q).presheaf.germ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) _ hyU').hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))) :=
      (EvalMatchLevel.stalkClosedPointTo_comp_germ y.1 (𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))))) ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) hyU' (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))).symm
    have hv2 : (Scheme.stalkClosedPointTo (y.1 ≫ 𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))))))).hom (((DRLevel.X N₀ q).presheaf.germ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) _ hyU').hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))) =
        (Scheme.stalkClosedPointTo (z ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))))).hom (((DRLevel.X N₀ q).presheaf.germ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) _ hgenU').hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))) := by
      have key : ∀ (q₁ q₂ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ DRLevel.X N₀ q) (e : q₁ = q₂)
          (h₁ : q₁.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
          (h₂ : q₂.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)),
          (Scheme.stalkClosedPointTo q₁).hom (((DRLevel.X N₀ q).presheaf.germ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) _ h₁).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))) =
            (Scheme.stalkClosedPointTo q₂).hom (((DRLevel.X N₀ q).presheaf.germ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) _ h₂).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))) := by
        rintro q₁ q₂ rfl h₁ h₂; rfl
      exact key _ _ hzt.symm hyU' hgenU'
    have hv3 : (Scheme.stalkClosedPointTo (z ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))))).hom (((DRLevel.X N₀ q).presheaf.germ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) _ hgenU').hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))) =
        (Scheme.stalkClosedPointTo z).hom (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hgenU).hom
          (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) :=
      EvalMatchLevel.stalkClosedPointTo_comp_germ z (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) hgenU' (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))
    have hv4 : val (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (t.base (IsLocalRing.closedPoint O)) hxfin).hom (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) = (Scheme.stalkClosedPointTo z).hom (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
        (z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hgenU).hom (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) := by
      rw [hval]
      exact EvalMatchLevel.map_stalkClosedPointTo_germ jK t ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) hxfin (by rw [← hz]; exact hgenU)
        (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))

    exact htransfer (rd (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (t.base (IsLocalRing.closedPoint O)) hxfin).hom (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))))) (⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull (N₀ * q))).2⟩ : ↥(modularFunctionFieldBar (N₀ * q))) hff (val (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (t.base (IsLocalRing.closedPoint O)) hxfin).hom (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))))) h1 (by rw [hres1, hv1, hv2, hv3, ← hv4])

  have Pclosure : ∀ r ∈ Subring.closure
      (Set.range (fun a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) => ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) (t.base (IsLocalRing.closedPoint O)) hxfin).hom
          (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) ∪
       Set.range (fun o : O => ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).presheaf.germ ⊤ (t.base (IsLocalRing.closedPoint O)) trivial).hom
          (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (ρO)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)))), Pr r := by
    intro r hr
    induction hr using Subring.closure_induction with
    | mem r hr =>
      rcases hr with ⟨a, rfl⟩ | ⟨o, rfl⟩
      · exact Pchart a
      · exact Pconst o
    | zero => exact Pzero
    | one => exact Pone
    | add _ _ _ _ h₁ h₂ => exact Padd _ _ h₁ h₂
    | neg _ _ h => exact Pneg _ h
    | mul _ _ _ _ h₁ h₂ => exact Pmul _ _ h₁ h₂

  obtain ⟨u, w, hwu, hsw, hu, hw⟩ := AlgebraicGeometry.exists_isUnit_mul_eq_mem_closure_of_stalk_pullback
    (DRLevel.toBase N₀ q) (IgusaScheme.ιFin (N₀ * q) q) (IgusaScheme.ιFin_igusaTo (N₀ * q) q)
    (t.base (IsLocalRing.closedPoint O)) hxfin s
  obtain ⟨hu1, eu⟩ := Pclosure u hu
  obtain ⟨hw1, ew⟩ := Pclosure w hw

  have hvw : val w ≠ 0 := by
    intro h0
    have hU : IsUnit (val w) := hwu.map val
    rw [h0] at hU
    exact not_isUnit_zero hU
  have hwunit : IsUnit (⟨rd w, hw1⟩ : V.toValuationSubring) := by
    by_contra hnu
    have hm : (⟨rd w, hw1⟩ : V.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← IsLocalRing.residue_eq_zero_iff, ew] at hm
    exact hvw ((map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) V.ResidueField).injective).mp hm)
  obtain ⟨hw0, hwinv⟩ := (EvalMatchLevel.isUnit_valuationSubring_mk_iff _ _ hw1).mp hwunit

  have hsw' : rd s * rd w = rd u := by rw [← map_mul, hsw]
  have hrds : rd s = rd u * (rd w)⁻¹ := by rw [← hsw', mul_inv_cancel_right₀ hw0]
  have hmemS : rd s ∈ V.toValuationSubring := by rw [hrds]; exact mul_mem hu1 hwinv
  have hresS : IsLocalRing.residue V.toValuationSubring ⟨rd s, hmemS⟩ =
      algebraMap (AlgebraicClosure ℚ) V.ResidueField (val s) := by
    have hprod : (⟨rd s, hmemS⟩ : V.toValuationSubring) * ⟨rd w, hw1⟩ = ⟨rd u, hu1⟩ := Subtype.ext hsw'
    have e := congrArg (IsLocalRing.residue V.toValuationSubring) hprod
    rw [map_mul, ew, eu] at e
    have hvals : val s * val w = val u := by rw [← map_mul, hsw]
    rw [← hvals, map_mul] at e
    exact mul_right_cancel₀ ((map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) V.ResidueField).injective).mpr hvw) e
  refine ⟨hmemS, ?_⟩
  show V.evalAt (rd s) = val s
  rw [Place.evalAt_of_mem _ hmemS, hresS]
  exact Place.residueInv_algebraMap _ _

end S_ModularCurve_DRModelPackageLevel_phi_mem_and_evalAt_eq_stalkClosedPointTo_of_section
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_phi_mem_and_evalAt_eq_stalkClosedPointTo_of_section (solution)
