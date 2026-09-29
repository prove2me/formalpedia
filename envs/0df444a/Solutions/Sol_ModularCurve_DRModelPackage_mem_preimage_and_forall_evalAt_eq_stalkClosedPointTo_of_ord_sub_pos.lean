-- Prove2me | solution 1 for ModularCurve.DRModelPackage.mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e4c665b7-075f-5e1e-be1f-5adee3163bcb

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_AlgebraicGeometry_exists_isUnit_mul_eq_mem_closure_of_stalk_pullback
import Theorems.Thm_ModularCurve_DRModelPackage_evalAt_eq_stalkClosedPointTo_of_schemeHomOver
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_DRModelPackage_mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos.ModularCurve ModularCurve.PlaceSpecialization"

namespace EvalMatch

universe u

theorem stalkClosedPointTo_germ_const {O : Type u} [CommRing O] [IsLocalRing O]
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

theorem stalkClosedPointTo_comp_germ {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}
    (q : Spec R ⟶ X) (g : X ⟶ Y) (U : Y.Opens) (hU : (q ≫ g).base (IsLocalRing.closedPoint R) ∈ U) (f : Γ(Y, U)) :
    (Scheme.stalkClosedPointTo (q ≫ g)).hom ((Y.presheaf.germ U _ hU).hom f) =
      (Scheme.stalkClosedPointTo q).hom ((X.presheaf.germ (g ⁻¹ᵁ U) (q.base (IsLocalRing.closedPoint R)) hU).hom
        ((g.app U).hom f)) := by
  rw [Scheme.stalkClosedPointTo_comp]
  show ((Y.presheaf.germ U _ hU ≫ g.stalkMap _) ≫ Scheme.stalkClosedPointTo q).hom f = _
  erw [Scheme.Hom.germ_stalkMap g U (q.base (IsLocalRing.closedPoint R)) hU]
  rfl

theorem map_stalkClosedPointTo_germ {O K' : Type u} [CommRing O] [IsLocalRing O] [CommRing K'] [IsLocalRing K']
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

theorem algebraMap_germ_eq_germToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U)
    [Nonempty U] (f : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ U x hx).hom f) = (X.germToFunctionField U).hom f := by
  change ((X.presheaf.germ U x hx) ≫ X.presheaf.stalkSpecializes _).hom f = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

theorem isUnit_valuationSubring_mk_iff {F : Type*} [Field F] (A : ValuationSubring F) (g : F) (hg : g ∈ A) :
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

theorem residue_eq_algebraMap_iff {K S : Type*} [Field K] [CommRing S] [IsLocalRing S] [Algebra K S] (x : S) (c : K) :
    IsLocalRing.residue S x = algebraMap K (IsLocalRing.ResidueField S) c ↔ ¬ IsUnit (x - algebraMap K S c) := by
  rw [show algebraMap K (IsLocalRing.ResidueField S) c = IsLocalRing.residue S (algebraMap K S c) from rfl,
    ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

end EvalMatch

namespace ModularCurve p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage ModularPolynomialData modularFunctionFieldFull IgusaScheme.jFull IgusaScheme coeffEmb modularFunctionFieldBar PlaceSpecialization.ProlongationTuple.jFun PlaceSpecialization.ProlongationTuple PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence DRModelPackage.evalAt_eq_stalkClosedPointTo_of_schemeHomOver isRational_place_modularFunctionFieldBar" namespace DRModelPackage p2m_export "ModularCurve.DRModelPackage" "eη Mη w evalAt_eq_stalkClosedPointTo_of_schemeHomOver" end ModularCurve.DRModelPackage
p2m_open_scoped "ModularCurve ModularCurve.DRModelPackage" in
set_option maxHeartbeats 16000000 in

theorem ModularCurve.DRModelPackage.section_closedPoint_mem_preimage_chartFin_of_hasValue
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    [hneη : Nonempty (Scheme.Opens.toScheme ((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (O : Type) [CommRing O] [IsLocalRing O]
    (K : Type) [Field K] [Algebra O K] (ιK : K →+* AlgebraicClosure ℚ)
    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (t : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (ht : Spec.map (CommRingCat.ofHom (ιK.comp (algebraMap O K))) ≫ t.1 ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = (𝔛.Mη.pointEquivPlace.symm (ePl V)).1 ≫ 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))))
    (b : AlgebraicClosure ℚ)
    (hjV : (ePl V).HasValue (𝔛.Mη.ffEquiv.symm (𝔛.Mη.C.germToFunctionField ((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
      (((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) b)
    (hb : ∀ m : O, m ∈ IsLocalRing.maximalIdeal O → ιK (algebraMap O K m) * b ≠ 1) :
    t.1.base (IsLocalRing.closedPoint O) ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
  classical

  set y := 𝔛.Mη.pointEquivPlace.symm (ePl V) with hy
  have hyV : 𝔛.Mη.pointEquivPlace y = ePl V := Equiv.apply_symm_apply _ _
  set jK : CommRingCat.of O ⟶ CommRingCat.of (AlgebraicClosure ℚ) := CommRingCat.ofHom (ιK.comp (algebraMap O K)) with hjK
  set z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := Spec.map jK ≫ t.1 with hz
  have hzt : z ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = y.1 ≫ 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) := by rw [hz, Category.assoc]; exact ht
  set Φ := 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) with hΦ

  by_contra hnot
  have hUeq : AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) = TwoChartIntegralModel.chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) := AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U_eq ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
  have hVeq : AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) = TwoChartIntegralModel.chartInfOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) := AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V_eq ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
  have hcov : t.1.base (IsLocalRing.closedPoint O) ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ⊔ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
    have e : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ⊔ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) = ⊤ := by
      show (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⊔ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) = ⊤
      rw [hUeq, hVeq]
      exact TwoChartIntegralModel.chartFinOpenBC_sup_chartInfOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O
    rw [e]; trivial
  have hI : t.1.base (IsLocalRing.closedPoint O) ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := (TopologicalSpace.Opens.mem_sup.mp hcov).resolve_left hnot

  have hgdef : (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))) = AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.g ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) := rfl
  have hnu : ¬ IsUnit (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hI).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))) := by
    intro hu
    apply hnot
    have hmem : t.1.base (IsLocalRing.closedPoint O) ∈ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).basicOpen (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) :=
      (Scheme.mem_basicOpen'' _ _ _).mpr ⟨hI, hu⟩
    rw [← Scheme.preimage_basicOpen, hgdef, AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.basicOpen_g, ← AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U_inf_V] at hmem
    exact hmem.1
  set θ := Scheme.stalkClosedPointTo t.1 with hθ
  have hm : θ.hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hI).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))) ∈
      IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (fun hu => hnu (isUnit_of_map_unit θ.hom _ hu))

  have hgenI : z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
    have hsp : (Spec.map jK).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ IsLocalRing.closedPoint O :=
      IsLocalRing.specializes_closedPoint _
    have hsp' : z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ t.1.base (IsLocalRing.closedPoint O) := by
      rw [hz, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
      exact hsp.map t.1.base.hom.continuous
    exact hsp'.mem_open ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).isOpen hI
  have hgenI' : (z ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := hgenI
  have hyI' : (y.1 ≫ 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by rw [← hzt]; exact hgenI'
  have hyI : y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := hyI'

  have hv1 : ιK (algebraMap O K (θ.hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hI).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))))) =
      (Scheme.stalkClosedPointTo z).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hgenI).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))) := by
    rw [hθ]
    exact EvalMatch.map_stalkClosedPointTo_germ jK t.1 ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) hI (by rw [← hz]; exact hgenI) (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))
  have hv2 : (Scheme.stalkClosedPointTo z).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hgenI).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))) =
      (Scheme.stalkClosedPointTo (z ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))).hom (((AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).presheaf.germ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ hgenI').hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) :=
    (EvalMatch.stalkClosedPointTo_comp_germ z (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) hgenI' (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))).symm
  have hv3 : (Scheme.stalkClosedPointTo (z ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))).hom (((AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).presheaf.germ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ hgenI').hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) =
      (Scheme.stalkClosedPointTo (y.1 ≫ 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))))).hom (((AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).presheaf.germ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ hyI').hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) := by
    have key : ∀ (q₁ q₂ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (_ : q₁ = q₂)
        (h₁ : q₁.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (h₂ : q₂.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        (Scheme.stalkClosedPointTo q₁).hom (((AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).presheaf.germ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ h₁).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) = (Scheme.stalkClosedPointTo q₂).hom (((AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).presheaf.germ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ h₂).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) := by
      rintro q₁ q₂ rfl h₁ h₂; rfl
    exact key _ _ hzt hgenI' hyI'
  have hv4 : (Scheme.stalkClosedPointTo (y.1 ≫ 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))))).hom (((AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).presheaf.germ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ hyI').hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) =
      (Scheme.stalkClosedPointTo y.1).hom ((𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyI).hom ((Φ.app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))) :=
    EvalMatch.stalkClosedPointTo_comp_germ y.1 Φ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) hyI' (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))

  set gI : Γ(𝔛.Mη.C, Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) := (Φ.app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))) with hgI
  set fF : Γ(𝔛.Mη.C, Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) := (Φ.app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))) with hfF
  have hL1 := AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo 𝔛.Mη y
    ((𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyI).hom gI)
  rw [hyV] at hL1
  obtain ⟨h1, hres1, -⟩ := hL1
  set c : AlgebraicClosure ℚ := ιK (algebraMap O K (θ.hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hI).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))))) with hcdef
  have hcval : (Scheme.stalkClosedPointTo y.1).hom ((𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyI).hom gI) = c := by
    rw [hv1, hv2, hv3, hv4]
  have hgval : (ePl V).HasValue (𝔛.Mη.ffEquiv.symm (algebraMap _ 𝔛.Mη.C.functionField
      ((𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyI).hom gI))) c :=
    ⟨h1, by rw [hres1, hcval]⟩

  haveI hneI : Nonempty (Scheme.Opens.toScheme (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))) := ⟨⟨_, hyI⟩⟩
  have hξF : genericPoint 𝔛.Mη.C ∈ Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) :=
    ((genericPoint_spec 𝔛.Mη.C).mem_open_set_iff (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).isOpen).mpr (let ⟨⟨q, hq⟩⟩ := hneη; ⟨q, trivial, hq⟩)
  have hξI : genericPoint 𝔛.Mη.C ∈ Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) :=
    ((genericPoint_spec 𝔛.Mη.C).mem_open_set_iff (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).isOpen).mpr ⟨_, trivial, hyI⟩
  have hprod : 𝔛.Mη.ffEquiv.symm (algebraMap _ 𝔛.Mη.C.functionField
        ((𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyI).hom gI)) *
      𝔛.Mη.ffEquiv.symm (𝔛.Mη.C.germToFunctionField (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) fF) = 1 := by
    rw [EvalMatch.algebraMap_germ_eq_germToFunctionField, ← map_mul, ← map_one 𝔛.Mη.ffEquiv.symm]
    congr 1

    have e0 := AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.res_f_mul_res_g ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    have e1 := congrArg (fun s => (𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⊓ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (genericPoint 𝔛.Mη.C) ⟨hξF, hξI⟩).hom
      ((Φ.app (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⊓ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).hom s)) e0
    simp only [map_mul, map_one] at e1

    have eF : (AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).presheaf.map (homOfLE (inf_le_left : AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⊓ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ≤ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).op ≫
        Φ.app (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⊓ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ≫ 𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⊓ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (genericPoint 𝔛.Mη.C) ⟨hξF, hξI⟩ =
        Φ.app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ≫ 𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (genericPoint 𝔛.Mη.C) hξF := by
      rw [Φ.naturality_assoc]
      erw [TopCat.Presheaf.germ_res]
    have eI : (AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).presheaf.map (homOfLE (inf_le_right : AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⊓ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ≤ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).op ≫
        Φ.app (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⊓ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ≫ 𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⊓ AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.V ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (genericPoint 𝔛.Mη.C) ⟨hξF, hξI⟩ =
        Φ.app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ≫ 𝔛.Mη.C.presheaf.germ (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (genericPoint 𝔛.Mη.C) hξI := by
      rw [Φ.naturality_assoc]
      erw [TopCat.Presheaf.germ_res]
    have eF' := congrArg (fun ψ => ψ.hom (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.f ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) eF
    have eI' := congrArg (fun ψ => ψ.hom (AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.g ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) eI
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at eF' eI'
    rw [eF', eI'] at e1

    rw [mul_comm]
    exact e1

  have h11 := hgval.mul hjV
  rw [hprod] at h11
  exact hb _ hm ((ePl V).hasValue_one.unique h11).symm

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_DRModelPackage_mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos.ModularCurve ModularCurve.PlaceSpecialization"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_DRModelPackage_mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos.ModularCurve _root_.ModularCurve.DRModelPackage _root_.P2MW.S_ModularCurve_DRModelPackage_mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos.ModularCurve.DRModelPackage in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)

    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
          (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')

    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))

    (hjint : ∃ a : A, 0 < V.ord (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ)))
    (t : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O)))
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (ht : Spec.map (CommRingCat.ofHom (ιK.comp (algebraMap O K))) ≫ t.1 ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      (𝔛.Mη.pointEquivPlace.symm (ePl V)).1 ≫ 𝔛.eη ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))
    (hx : t.1.base (IsLocalRing.closedPoint O) = x)
    :
    x ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ∧
    ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
      (t.1.base (IsLocalRing.closedPoint O)),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
          ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr
            (.of_eq hx) |>.hom.hom s)) ∈ V.toValuationSubring ∧
      V.evalAt (φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
          ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr
            (.of_eq hx) |>.hom.hom s))) =
        ιK (algebraMap O K (Scheme.stalkClosedPointTo t.1 s)) := by
  classical
  haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨a, ha⟩ := hjint

  have hvalOf : ∀ {K' F' : Type} [Field K'] [Field F'] [Algebra K' F'] (v : Place K' F') (g : F') (c : K'),
      0 < v.ord (g - algebraMap K' F' c) → v.HasValue g c := by
    intro K' F' _ _ _ v g c hord
    have hne0 : g - algebraMap K' F' c ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hord; exact lt_irrefl _ hord
    have hmem : g - algebraMap K' F' c ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hne0 hord.le
    have hmax := Place.mk_mem_maximalIdeal_of_ord_pos v hmem hord
    have hc := (v.hasValue_algebraMap c)
    have hg : g ∈ v.toValuationSubring := by
      have : g = (g - algebraMap K' F' c) + algebraMap K' F' c := by ring
      rw [this]; exact add_mem hmem hc.mem
    refine ⟨hg, ?_⟩
    have e : (⟨g, hg⟩ : v.toValuationSubring) = ⟨g - algebraMap K' F' c, hmem⟩ + ⟨algebraMap K' F' c, hc.mem⟩ := by
      apply Subtype.ext; show g = (g - _) + _; ring
    rw [e, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add, hc.residue_eq]
  have hVj : V.HasValue (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p) (a : AlgebraicClosure ℚ) :=
    hvalOf V _ _ ha

  set jη : ↥(modularFunctionFieldBar p) := 𝔛.Mη.ffEquiv.symm (𝔛.Mη.C.germToFunctionField
      ((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
      (((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))).app
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
        (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv
            (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))) with hjη
  have hseries : ((ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p : ↥(modularFunctionFieldBar (1 * p))) :
      LaurentSeries (AlgebraicClosure ℚ)) = (jη : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hjη, hMη]
    rfl
  obtain ⟨hmemiff, hevaleq⟩ := hePl V _ _ hseries
  have hVrat : V.IsRational := ModularCurve.isRational_place_modularFunctionFieldBar (1 * p) V
  have hWrat : (ePl V).IsRational := ModularCurve.isRational_place_modularFunctionFieldBar p (ePl V)
  have hjηmem : jη ∈ (ePl V).toValuationSubring := hmemiff.mp hVj.mem
  have hevalV : V.evalAt (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p) = (a : AlgebraicClosure ℚ) := by
    rw [Place.evalAt_of_mem _ hVj.mem, hVj.residue_eq, Place.residueInv_algebraMap]
  have hjV : (ePl V).HasValue jη (a : AlgebraicClosure ℚ) := by
    refine ⟨hjηmem, ?_⟩
    rw [← Place.algebraMap_evalAt _ hWrat hjηmem, ← hevaleq, hevalV]

  have hb : ∀ m : O, m ∈ IsLocalRing.maximalIdeal O → ιK (algebraMap O K m) * (a : AlgebraicClosure ℚ) ≠ 1 := by
    intro m hm h1
    rw [hϖ, Ideal.mem_span_singleton'] at hm
    obtain ⟨m', rfl⟩ := hm
    have hcA : ιK (algebraMap O K m') ∈ A := hιA m'

    have hunit : IsUnit ((p : ℕ) : ↥A) := by
      refine IsUnit.of_mul_eq_one (⟨ιK (algebraMap O K m'), hcA⟩ * a) ?_
      apply Subtype.ext
      rw [map_mul, map_mul, map_natCast, map_natCast] at h1
      have : ((p : ℕ) : AlgebraicClosure ℚ) * (ιK (algebraMap O K m') * (a : AlgebraicClosure ℚ)) = 1 := by
        rw [← h1]; ring
      simpa using this
    have hred : IsUnit (red ((p : ℕ) : ↥A)) := hunit.map red
    rw [map_natCast, CharP.cast_eq_zero] at hred
    exact not_isUnit_zero hred
  have hfin₀ := ModularCurve.DRModelPackage.section_closedPoint_mem_preimage_chartFin_of_hasValue p 𝔛 O K ιK ePl V t ht
    (a : AlgebraicClosure ℚ) hjV hb
  have hfin : x ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := hx ▸ hfin₀
  exact ⟨hfin, fun s => ModularCurve.DRModelPackage.evalAt_eq_stalkClosedPointTo_of_schemeHomOver p hp 𝔛 hMη O hϖ K ιK x φ hφO hφj
    P R ePl hePl V t ht hx hfin s⟩

end S_ModularCurve_DRModelPackage_mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos (solution)
