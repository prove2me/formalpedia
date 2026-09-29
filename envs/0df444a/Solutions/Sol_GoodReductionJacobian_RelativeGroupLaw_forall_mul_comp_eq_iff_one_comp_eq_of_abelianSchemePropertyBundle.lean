-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/39a9b580-5f2b-5284-9962-bbedf746b96d

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace K63H4a

theorem lift_one_eq {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {S' : Type} [CommRing S']
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (h1 : (L.one (t' ≫ s)).1 ≫ f = t' ≫ s) (h2 : (L.one s).1 ≫ f = 𝟙 _ ≫ s) :
    pullback.lift (L.one (t' ≫ s)).1 t' h1 = t' ≫ pullback.lift (L.one s).1 (𝟙 _) h2 := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    have h := congrArg Subtype.val (L.one_natural s (t' ≫ s) t' rfl)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
    exact h.symm
  · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]

end K63H4a

theorem solution
    (S : Type) [CommRing S] {A B : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) (g : B ⟶ Spec (CommRingCat.of S))
    (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
    (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f) (hB : AbelianSchemePropertyBundle S g)
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
          (LB.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) ↔
      pullback.lift (LA.one s).1 (𝟙 _) (by rw [Category.id_comp]; exact (LA.one s).2) ≫ φ = (LB.one s).1 := by

  let LA' := LA.baseChange s
  let LB' := LB.baseChange s
  have hA' : AbelianSchemePropertyBundle S' (pullback.snd f s) :=
    hA.of_isPullback (IsPullback.of_hasPullback f s)
  have hB' : AbelianSchemePropertyBundle S' (pullback.snd g s) :=
    hB.of_isPullback (IsPullback.of_hasPullback g s)
  let φ' : SchemeHomOver (pullback.snd f s) (pullback.snd g s) :=
    ⟨pullback.lift φ (pullback.snd f s) hφ, pullback.lift_snd _ _ _⟩
  constructor
  ·
    intro hmul
    have h := hmul (Spec (CommRingCat.of S')) (𝟙 _) (LA.one (𝟙 _ ≫ s)) (LA.one (𝟙 _ ≫ s))
    simp only [LA.one_mul] at h

    set Z : SchemeHomOver (𝟙 _ ≫ s) g :=
      ⟨pullback.lift (LA.one (𝟙 _ ≫ s)).1 (𝟙 _) (LA.one (𝟙 _ ≫ s)).2 ≫ φ, by
        rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩ with hZ
    have hZZ : LB.mul _ Z Z = Z := (Subtype.ext h).symm
    have hZ1 : Z = LB.one (𝟙 _ ≫ s) := by
      calc Z = LB.mul _ (LB.one _) Z := (LB.one_mul _ _).symm
        _ = LB.mul _ (LB.mul _ (LB.inv _ Z) Z) Z := by rw [LB.inv_mul_cancel]
        _ = LB.mul _ (LB.inv _ Z) (LB.mul _ Z Z) := by rw [LB.mul_assoc]
        _ = LB.mul _ (LB.inv _ Z) Z := by rw [hZZ]
        _ = LB.one _ := LB.inv_mul_cancel _ _
    have hZ1' := congrArg Subtype.val hZ1
    rw [hZ] at hZ1'
    dsimp only at hZ1'
    have hB1 := congrArg Subtype.val (LB.one_natural s (𝟙 _ ≫ s) (𝟙 _) rfl)
    rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at hB1
    rw [K63H4a.lift_one_eq LA s (𝟙 _) (LA.one (𝟙 _ ≫ s)).2
        (by rw [Category.id_comp]; exact (LA.one s).2), Category.id_comp, ← hB1] at hZ1'
    exact hZ1'
  ·
    intro hunit
    have hφ' : NeronModelInfra.schemeHomOverComp (LA'.one (𝟙 _)) φ' = LB'.one (𝟙 _) := by
      apply Subtype.ext
      rw [NeronModelInfra.schemeHomOverComp_coe]
      apply pullback.hom_ext
      · simp only [LA', LB', φ', RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe,
          Category.assoc, pullback.lift_fst]
        rw [K63H4a.lift_one_eq LA s (𝟙 _) (LA.one (𝟙 _ ≫ s)).2 (by rw [Category.id_comp]; exact (LA.one s).2),
          Category.id_comp, hunit]
        have hB1 := congrArg Subtype.val (LB.one_natural s (𝟙 _ ≫ s) (𝟙 _) rfl)
        rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at hB1
        exact hB1
      · simp only [φ', Category.assoc, pullback.lift_snd]
        rw [(LA'.one (𝟙 _)).2, (LB'.one (𝟙 _)).2]
    intro T t' P Q
    let x : SchemeHomOver t' (pullback.snd f s) := RelativeGroupLaw.baseChangePointOfBase s P
    let y : SchemeHomOver t' (pullback.snd f s) := RelativeGroupLaw.baseChangePointOfBase s Q
    have Hxy := congrArg (fun z => z.1 ≫ pullback.fst g s)
      (hA'.schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one hB' LA' LB' φ' hφ' t' x y)
    simp only [NeronModelInfra.schemeHomOverComp_coe, LA', LB', x, y, φ', RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointOfBase_coe, RelativeGroupLaw.baseChangePointToBase_ofBase,
      Category.assoc, pullback.lift_fst] at Hxy
    rw [Hxy]
    congr 2 <;> apply Subtype.ext <;>
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
        RelativeGroupLaw.baseChangePointOfBase_coe, Category.assoc, pullback.lift_fst]

end S_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle (solution)
