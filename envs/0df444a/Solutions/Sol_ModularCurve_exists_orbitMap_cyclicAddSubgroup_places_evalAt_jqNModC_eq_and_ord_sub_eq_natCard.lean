-- Prove2me | solution 1 for ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8921fd36-fe63-5ed5-a00a-5ffb08860299

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard
import Theorems.Thm_WeierstrassCurve_natCard_variableChange_stabilizer_eq_of_fullKernelQuotient
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_finite_stabilizer_variableChange
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.Gamma0Pair.isElliptic ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000

p2m_open "WeierstrassCurve WeierstrassCurve.Affine ModularCurve~CycSub AlgebraicCurve"
open scoped IntermediateField

noncomputable section

namespace P2MKcA
namespace DAssembly

section AutPt

variable {L : Type*} [Field L] [DecidableEq L]

def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

def autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

theorem autPt_apply {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_eq_iff_heq {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

theorem autPt_injective {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    Function.Injective (autPt γ hγ) := by
  intro P Q h
  rw [autPt_apply, autPt_apply] at h
  exact (Point.vcFun_rightInverse (C := γ) (W := W.toAffine)).injective ((castPt hγ).injective h)

end AutPt

section CycSub

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] (N : ℕ)

private abbrev _root_.P2MKcA.DAssembly.CycSub (A : Type*) [AddCommGroup A] (N : ℕ) : Type _ :=
  {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N}

p2m_export "P2MKcA.DAssembly" "CycSub"
variable {N}

private theorem _root_.P2MKcA.DAssembly.exists_generator (hN : N ≠ 0) (H : CycSub A N) :
    ∃ g : A, addOrderOf g = N ∧ AddSubgroup.zmultiples g = H.1 := by
  obtain ⟨hc, hcard⟩ := H.2
  haveI := hc
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H.1)
  have hfin : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  have hog : addOrderOf g = N := (addOrderOf_eq_card_of_forall_mem_zmultiples hg).trans hcard
  refine ⟨g.1, by rw [AddSubgroup.addOrderOf_coe, hog], ?_⟩
  have hle : AddSubgroup.zmultiples (g.1) ≤ H.1 := by
    rw [AddSubgroup.zmultiples_le]; exact g.2
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, Nat.card_zmultiples, AddSubgroup.addOrderOf_coe, hog]

p2m_export "P2MKcA.DAssembly" "exists_generator"

def cycOf (g : A) (hg : addOrderOf g = N) : CycSub A N :=
  ⟨AddSubgroup.zmultiples g, ⟨⟨g, AddSubgroup.mem_zmultiples g⟩, fun y => by
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩, by rw [Nat.card_zmultiples, hg]⟩

theorem nsmul_eq_zero_of_mem (H : CycSub A N) {x : A} (hx : x ∈ H.1) : N • x = 0 := by
  have h : Nat.card H.1 • (⟨x, hx⟩ : H.1) = 0 := card_nsmul_eq_zero'
  rw [H.2.2] at h
  exact congrArg Subtype.val h

def mapCyc (φ : A →+ B) (H : CycSub A N) (hφ : Set.InjOn φ H.1) : CycSub B N := by
  refine ⟨H.1.map φ, ?_, ?_⟩
  · obtain ⟨hc, -⟩ := H.2
    haveI := hc
    obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H.1)
    refine ⟨⟨⟨φ g.1, AddSubgroup.mem_map_of_mem φ g.2⟩, fun y => ?_⟩⟩
    obtain ⟨x, hx, hxy⟩ := AddSubgroup.mem_map.mp y.2
    obtain ⟨n, hn⟩ := hg ⟨x, hx⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hn' : n • g.1 = x := congrArg Subtype.val hn
    simp only [AddSubgroup.coe_zsmul, ← hxy, ← hn', map_zsmul]
  · have h := Nat.card_image_of_injOn hφ
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
    have hc : Nat.card (H.1.map φ) = Nat.card H.1 := by
      rw [← SetLike.coe_sort_coe, ← SetLike.coe_sort_coe H.1, Nat.card_coe_set_eq,
        Nat.card_coe_set_eq, AddSubgroup.coe_map]
      exact h
    exact hc.trans H.2.2

@[scoped simp] theorem mapCyc_val (φ : A →+ B) (H : CycSub A N) (hφ : Set.InjOn φ H.1) :
    (mapCyc φ H hφ).1 = H.1.map φ := rfl

def tors (A : Type*) [AddCommGroup A] (N : ℕ) : Set A := {x | N • x = 0}

theorem subset_tors (H : CycSub A N) : (H.1 : Set A) ⊆ tors A N :=
  fun _ hx => nsmul_eq_zero_of_mem H hx

theorem injOn_of_injOn_tors {φ : A →+ B} (hφ : Set.InjOn φ (tors A N)) (H : CycSub A N) :
    Set.InjOn φ H.1 :=
  hφ.mono (subset_tors H)

theorem mapCyc_injective {φ : A →+ B} (hφ : Set.InjOn φ (tors A N)) {H H' : CycSub A N}
    (h : mapCyc φ H (injOn_of_injOn_tors hφ H) = mapCyc φ H' (injOn_of_injOn_tors hφ H')) :
    H = H' := by
  have h1 : (φ '' (H.1 : Set A)) = φ '' (H'.1 : Set A) := by
    have := congrArg (fun X : CycSub B N => ((X.1 : AddSubgroup B) : Set B)) h
    simpa only [mapCyc_val, AddSubgroup.coe_map] using this
  have h2 : (H.1 : Set A) = H'.1 := (hφ.image_eq_image_iff (subset_tors H) (subset_tors H')).mp h1
  exact Subtype.ext (SetLike.coe_injective h2)

theorem mapCyc_surjective (hN : N ≠ 0) {φ : A →+ B} (hφ : Set.InjOn φ (tors A N))
    (hsurj : ∀ y ∈ tors B N, ∃ x ∈ tors A N, φ x = y) (H₀ : CycSub B N) :
    ∃ H : CycSub A N, mapCyc φ H (injOn_of_injOn_tors hφ H) = H₀ := by
  obtain ⟨g₀, hg₀, hgen⟩ := exists_generator hN H₀
  have hg₀t : g₀ ∈ tors B N := by
    show N • g₀ = 0
    rw [← hg₀]; exact addOrderOf_nsmul_eq_zero g₀
  obtain ⟨g, hgt, hgφ⟩ := hsurj g₀ hg₀t
  have hordg : addOrderOf g = N := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hgt) ?_
    rw [← hg₀, ← hgφ]
    exact addOrderOf_map_dvd φ g
  refine ⟨cycOf g hordg, Subtype.ext ?_⟩
  show (AddSubgroup.zmultiples g).map φ = H₀.1
  rw [AddMonoidHom.map_zmultiples, hgφ, hgen]

theorem eq_of_le_of_card_eq {H H' : AddSubgroup B} (hle : H ≤ H') (hH : Nat.card H = N)
    (hH' : Nat.card H' = N) (hN : N ≠ 0) : H = H' := by
  haveI : Finite H' := Nat.finite_of_card_ne_zero (by rw [hH']; exact hN)
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [hH, hH'])

theorem map_neg_eq (H : AddSubgroup B) : H.map (-(AddMonoidHom.id B)) = H := by
  ext x
  simp only [AddSubgroup.mem_map, AddMonoidHom.neg_apply, AddMonoidHom.id_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact H.neg_mem hy
  · intro hx; exact ⟨-x, H.neg_mem hx, neg_neg x⟩

end CycSub

section Assemble

variable {L : Type*} [Field L] [DecidableEq L] {E₀ : WeierstrassCurve L} {N : ℕ}
variable {Pt : Type*} [AddCommGroup Pt]
variable {G : Type*}
variable {X : Type*}
variable {Pl : Type*}

def Rel (E₀ : WeierstrassCurve L) (N : ℕ) (H H' : CycSub E₀.toAffine.Point N) : Prop :=
  ∃ γ : VariableChange L, γ • E₀ = E₀ ∧
    ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'

theorem Rel_iff (H H' : CycSub E₀.toAffine.Point N) :
    Rel E₀ N H H' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • E₀ = E₀, ∀ T ∈ H.1, autPt γ hγ T ∈ H'.1 := by
  unfold Rel
  constructor
  · rintro ⟨γ, hγ, h⟩
    refine ⟨γ, hγ, fun T hT => ?_⟩
    obtain ⟨T', hT', hh⟩ := h T hT
    rwa [(autPt_eq_iff_heq γ hγ T T').mpr hh]
  · rintro ⟨γ, hγ, h⟩
    exact ⟨γ, hγ, fun T hT => ⟨autPt γ hγ T, h T hT, (autPt_eq_iff_heq γ hγ T _).mp rfl⟩⟩

theorem Rel_iff_map_eq (hN : N ≠ 0) (H H' : CycSub E₀.toAffine.Point N) :
    Rel E₀ N H H' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • E₀ = E₀, H.1.map (autPt γ hγ) = H'.1 := by
  rw [Rel_iff]
  refine exists_congr fun γ => exists_congr fun hγ => ?_
  constructor
  · intro h
    have hle : H.1.map (autPt γ hγ) ≤ H'.1 := by
      rintro _ ⟨T, hT, rfl⟩; exact h T hT
    have hcard : Nat.card (H.1.map (autPt γ hγ)) = N :=
      (mapCyc (autPt γ hγ) H ((autPt_injective γ hγ).injOn)).2.2
    exact eq_of_le_of_card_eq hle hcard H'.2.2 hN
  · intro h T hT
    rw [← h]; exact AddSubgroup.mem_map_of_mem _ hT

theorem assemble (hN : N ≠ 0)
    (θ : Pt →+ E₀.toAffine.Point) (hθ : Set.InjOn θ (tors Pt N))
    (hθs : ∀ y ∈ tors E₀.toAffine.Point N, ∃ x ∈ tors Pt N, θ x = y)
    (D : G → Prop) (act : G → (Pt →+ Pt)) (hact : ∀ σ, Function.Injective (act σ))
    (ρ : G → VariableChange L) (hρ : ∀ σ, D σ → ρ σ • E₀ = E₀)
    (hequiv : ∀ σ (hσ : D σ) (P : Pt), θ (act σ P) = autPt (ρ σ) (hρ σ hσ) (θ P))
    (hsurj : ∀ (γ : VariableChange L) (hγ : γ • E₀ = E₀), ∃ σ, D σ ∧
      ((∀ P, θ (act σ P) = autPt γ hγ (θ P)) ∨ (∀ P, θ (act σ P) = -autPt γ hγ (θ P))))
    (Φ : CycSub Pt N ≃ X) (actX : G → X → X)
    (hnat : ∀ σ (H : CycSub Pt N), Φ (mapCyc (act σ) H (hact σ).injOn) = actX σ (Φ H))
    (π : X → Pl) (S : Finset Pl) (hπS : ∀ x, π x ∈ S) (hπsurj : ∀ P ∈ S, ∃ x, π x = P)
    (hπfib : ∀ x x', π x = π x' ↔ ∃ σ, D σ ∧ x' = actX σ x)
    (e : Pl → ℤ) (hπe : ∀ x, e (π x) = Nat.card {x' // π x' = π x}) :
    ∃ (Ξ : CycSub Pt N ≃ CycSub E₀.toAffine.Point N) (ε : CycSub E₀.toAffine.Point N ≃ X),
      (∀ H, (Ξ H).1 = H.1.map θ) ∧ ε = Ξ.symm.trans Φ ∧
      (∀ H, π (ε H) ∈ S) ∧ (∀ P ∈ S, ∃ H, π (ε H) = P) ∧
      (∀ H H', π (ε H) = π (ε H') ↔ Rel E₀ N H H') ∧
      ∀ H, e (π (ε H)) = Nat.card {H' // π (ε H') = π (ε H)} := by
  classical

  let Ξf : CycSub Pt N → CycSub E₀.toAffine.Point N := fun H => mapCyc θ H (injOn_of_injOn_tors hθ H)
  have hΞ : Function.Bijective Ξf :=
    ⟨fun H H' h => mapCyc_injective hθ h, fun H₀ => mapCyc_surjective hN hθ hθs H₀⟩
  let Ξ : CycSub Pt N ≃ CycSub E₀.toAffine.Point N := Equiv.ofBijective Ξf hΞ
  have Ξ_val : ∀ H, (Ξ H).1 = H.1.map θ := fun H => rfl

  let ε : CycSub E₀.toAffine.Point N ≃ X := Ξ.symm.trans Φ
  refine ⟨Ξ, ε, Ξ_val, rfl, fun H₀ => hπS _, ?_, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨x, hx⟩ := hπsurj P hP
    exact ⟨ε.symm x, by simp only [Equiv.apply_symm_apply, hx]⟩
  ·
    intro H₀ H₀'
    rw [hπfib, Rel_iff_map_eq hN]

    have key : ∀ σ (hσ : D σ) (H : CycSub Pt N),
        (Ξ (mapCyc (act σ) H (hact σ).injOn)).1 = (Ξ H).1.map (autPt (ρ σ) (hρ σ hσ)) := by
      intro σ hσ H
      rw [Ξ_val, Ξ_val, mapCyc_val, AddSubgroup.map_map, AddSubgroup.map_map]
      congr 1
      ext P
      exact hequiv σ hσ P
    constructor
    · rintro ⟨σ, hσ, hx⟩

      have h1 : Φ (Ξ.symm H₀') = Φ (mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn) := by
        rw [hnat]; exact hx
      have h2 : Ξ.symm H₀' = mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn := Φ.injective h1
      refine ⟨ρ σ, hρ σ hσ, ?_⟩
      have h3 := key σ hσ (Ξ.symm H₀)
      rw [← h2, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h3
      exact h3.symm
    · rintro ⟨γ, hγ, hmap⟩
      obtain ⟨σ, hσ, hsgn⟩ := hsurj γ hγ
      refine ⟨σ, hσ, ?_⟩

      have h1 : (Ξ (mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn)).1 = H₀'.1 := by
        rw [Ξ_val, mapCyc_val, AddSubgroup.map_map]
        have hH₀ : (Ξ.symm H₀).1.map θ = H₀.1 := by
          rw [← Ξ_val, Equiv.apply_symm_apply]
        rcases hsgn with h | h
        · have hc : θ.comp (act σ) = (autPt γ hγ).comp θ := by ext P; exact h P
          rw [hc, ← AddSubgroup.map_map, hH₀, hmap]
        · have hc : θ.comp (act σ) = (-(AddMonoidHom.id _)).comp ((autPt γ hγ).comp θ) := by
            ext P; simp [h P]
          rw [hc, ← AddSubgroup.map_map, ← AddSubgroup.map_map, hH₀, hmap, map_neg_eq]
      have h2 : Ξ (mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn) = H₀' := Subtype.ext h1
      show Φ (Ξ.symm H₀') = actX σ (Φ (Ξ.symm H₀))
      rw [← hnat, ← h2, Equiv.symm_apply_apply]
  ·
    intro H₀
    rw [hπe]
    congr 1
    exact Nat.card_congr ((Equiv.subtypeEquiv ε (fun H₀' => Iff.rfl)).symm)

end Assemble

section Supplies

theorem isIntegral_of_apply_eq {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F]
    [Algebra K M] (x : F) (t : M) [FiniteDimensional K⟮t⟯ M] (ψ : F →ₐ[K] M) (hψ : ψ x = t) :
    ψ.toRingHom.IsIntegral := by
  intro y
  have hy : IsIntegral K⟮t⟯ y := Algebra.IsIntegral.isIntegral y
  obtain ⟨q, hqm, hq0⟩ := hy

  have hle : K⟮t⟯ ≤ ψ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨x, hψ⟩

  have hlifts : q.map (algebraMap K⟮t⟯ M) ∈ Polynomial.lifts ψ.toRingHom := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
    rw [Polynomial.coeff_map]
    obtain ⟨f, hf⟩ := hle (q.coeff n).2
    exact ⟨f, hf⟩
  obtain ⟨q', hq'map, -, hq'monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts (hqm.map _)
  refine ⟨q', hq'monic, ?_⟩
  rw [← Polynomial.eval_map, hq'map, Polynomial.eval_map]
  exact hq0

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

theorem tors_facts (E₀ : WeierstrassCurve K) [E₀.IsElliptic] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) :
    Nat.card (tors E₀.toAffine.Point N) = N ^ 2 ∧ ∃ g : E₀.toAffine.Point, addOrderOf g = N := by
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) E₀ hN
  have hb : (E₀⁄K) = E₀.toAffine := by
    show (E₀.baseChange K).toAffine = E₀.toAffine
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hb] at eT
  have hmem : ∀ P : E₀.toAffine.Point, P ∈ Submodule.torsionBy ℤ E₀.toAffine.Point N ↔ P ∈ tors _ N := by
    intro P
    rw [Submodule.mem_torsionBy_iff]
    show ((N : ℤ) • P = 0) ↔ N • P = 0
    rw [natCast_zsmul]
  have hset : (Submodule.torsionBy ℤ E₀.toAffine.Point N : Set E₀.toAffine.Point) = tors _ N :=
    Set.ext hmem
  constructor
  · have h1 : Nat.card (Submodule.torsionBy ℤ E₀.toAffine.Point N) = N ^ 2 := by
      rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
    rw [← SetLike.coe_sort_coe, hset] at h1
    exact h1
  · refine ⟨(eT (1, 0)).1, ?_⟩
    have h1 : addOrderOf ((eT (1, 0)).1) = addOrderOf (eT (1, 0)) :=
      addOrderOf_injective (Submodule.torsionBy ℤ E₀.toAffine.Point N).subtype.toAddMonoidHom
        Subtype.val_injective (eT (1, 0))
    rw [h1, AddEquiv.addOrderOf_eq eT, Prod.addOrderOf_mk, ZMod.addOrderOf_one, addOrderOf_zero,
      Nat.lcm_one_right]

end Supplies

end P2MKcA.DAssembly
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA"

namespace WInvOrb

variable {K : Type*} [Field K] [DecidableEq K]

def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

def autPt {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

theorem autPt_apply {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_eq_iff_heq {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

theorem heq_some {V V' : WeierstrassCurve.Affine K} (hV : V' = V) {x y : K}
    {h : V.Nonsingular x y} {h' : V'.Nonsingular x y} :
    HEq (Point.some x y h' : V'.Point) (Point.some x y h : V.Point) := by
  subst hV; rfl

theorem some_eq_some {V : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂) {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem nonsingular_vcInv {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    {x y : K} (h : W.toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular (vcXInv γ x) (vcYInv γ x y) := by
  have h' : (γ • W).toAffine.Nonsingular (vcXInv γ x) (vcYInv γ x y) :=
    (nonsingular_variableChange_iff (vcXInv γ x) (vcYInv γ x y)).mpr
      (by rwa [vcX_vcXInv, vcY_vcYInv])
  rwa [hγ] at h'

theorem autPt_some {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W) {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    autPt γ hγ (.some x y h) = .some (vcXInv γ x) (vcYInv γ x y) (nonsingular_vcInv γ hγ h) := by
  rw [autPt_eq_iff_heq]
  show HEq (Point.some (vcXInv γ x) (vcYInv γ x y) _ : (γ • W).toAffine.Point) _
  exact heq_some (congrArg WeierstrassCurve.toAffine hγ)

abbrev Aut (W : WeierstrassCurve K) : Subgroup (VariableChange K) :=
  MulAction.stabilizer (VariableChange K) W

theorem smul_eq_of_mem_Aut {W : WeierstrassCurve K} (γ : Aut W) : (γ : VariableChange K) • W = W :=
  MulAction.mem_stabilizer_iff.mp γ.2

theorem one_u : (1 : VariableChange K).u = 1 := rfl
theorem one_r : (1 : VariableChange K).r = 0 := rfl
theorem one_s : (1 : VariableChange K).s = 0 := rfl
theorem one_t : (1 : VariableChange K).t = 0 := rfl
theorem mul_u (C C' : VariableChange K) : (C * C').u = C.u * C'.u := rfl
theorem mul_r (C C' : VariableChange K) : (C * C').r = C.r * C'.u ^ 2 + C'.r := rfl
theorem mul_s (C C' : VariableChange K) : (C * C').s = C'.u * C.s + C'.s := rfl
theorem mul_t (C C' : VariableChange K) :
    (C * C').t = C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t := rfl

theorem vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  rw [vcXInv, one_u, one_r]; simp

theorem vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  rw [vcYInv, one_u, one_r, one_s, one_t]; simp

theorem vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, mul_u, mul_r, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

theorem vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, mul_u, mul_r, mul_s, mul_t, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

scoped instance instMulActionAutPoint (W : WeierstrassCurve K) : MulAction (Aut W) W.toAffine.Point where
  smul γ P := autPt γ.1 (smul_eq_of_mem_Aut γ) P
  one_smul P := by
    change autPt (1 : VariableChange K) _ P = P
    rcases P with _ | ⟨x, y, h⟩
    · exact map_zero (autPt (1 : VariableChange K) _)
    · rw [autPt_some]
      exact some_eq_some (vcXInv_one x) (vcYInv_one x y)
  mul_smul γ δ P := by
    change autPt (γ.1 * δ.1) _ P = autPt γ.1 _ (autPt δ.1 _ P)
    rcases P with _ | ⟨x, y, h⟩
    · show autPt (γ.1 * δ.1) _ 0 = autPt γ.1 _ (autPt δ.1 _ 0)
      simp only [map_zero]
    · rw [autPt_some, autPt_some, autPt_some]
      exact some_eq_some (vcXInv_mul _ _ x) (vcYInv_mul _ _ x y)

theorem aut_smul_def {W : WeierstrassCurve K} (γ : Aut W) (P : W.toAffine.Point) :
    γ • P = autPt γ.1 (smul_eq_of_mem_Aut γ) P := rfl

scoped instance instDistribMulActionAutPoint (W : WeierstrassCurve K) :
    DistribMulAction (Aut W) W.toAffine.Point where
  smul_zero γ := map_zero (autPt γ.1 (smul_eq_of_mem_Aut γ))
  smul_add γ P Q := map_add (autPt γ.1 (smul_eq_of_mem_Aut γ)) P Q

open scoped Pointwise

abbrev CycSub (W : WeierstrassCurve K) (N : ℕ) : Type _ :=
  {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}

theorem natCard_smul_addSubgroup {W : WeierstrassCurve K} (γ : Aut W) (H : AddSubgroup W.toAffine.Point) :
    Nat.card (γ • H : AddSubgroup W.toAffine.Point) = Nat.card H := by
  rw [AddSubgroup.pointwise_smul_def]
  exact (Nat.card_congr (H.equivMapOfInjective _ (MulAction.injective γ)).toEquiv).symm

theorem isAddCyclic_smul_addSubgroup {W : WeierstrassCurve K} (γ : Aut W)
    (H : AddSubgroup W.toAffine.Point) [hH : IsAddCyclic H] :
    IsAddCyclic (γ • H : AddSubgroup W.toAffine.Point) := by
  rw [AddSubgroup.pointwise_smul_def]
  exact isAddCyclic_of_surjective (H.equivMapOfInjective _ (MulAction.injective γ))
    (H.equivMapOfInjective _ (MulAction.injective γ)).surjective

scoped instance instMulActionAutCycSub (W : WeierstrassCurve K) (N : ℕ) : MulAction (Aut W) (CycSub W N) where
  smul γ H := ⟨γ • H.1, ⟨by haveI := H.2.1; exact isAddCyclic_smul_addSubgroup γ H.1,
    (natCard_smul_addSubgroup γ H.1).trans H.2.2⟩⟩
  one_smul H := Subtype.ext (one_smul (Aut W) H.1)
  mul_smul γ δ H := Subtype.ext (mul_smul γ δ H.1)

theorem coe_smul_cycSub {W : WeierstrassCurve K} {N : ℕ} (γ : Aut W) (H : CycSub W N) :
    ((γ • H : CycSub W N) : AddSubgroup W.toAffine.Point) = γ • (H : AddSubgroup W.toAffine.Point) := rfl

theorem rel_iff_mem_orbit {W : WeierstrassCurve K} {N : ℕ} [NeZero N] (H H' : CycSub W N) :
    (∃ γ : VariableChange K, γ • W = W ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T') ↔
      H' ∈ MulAction.orbit (Aut W) H := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    let g : Aut W := ⟨γ, MulAction.mem_stabilizer_iff.mpr hγ⟩
    have hle : (g • H.1 : AddSubgroup W.toAffine.Point) ≤ H'.1 := by
      intro P hP
      obtain ⟨T, hT, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists P g H.1).mp hP
      obtain ⟨T', hT', hh⟩ := h T hT
      have : g • T = T' := (autPt_eq_iff_heq γ hγ T T').mpr hh
      rwa [this]
    haveI : Finite H'.1 := Nat.finite_of_card_ne_zero (by rw [H'.2.2]; exact NeZero.ne N)
    have heq : (g • H.1 : AddSubgroup W.toAffine.Point) = H'.1 :=
      AddSubgroup.eq_of_le_of_card_ge hle (by rw [natCard_smul_addSubgroup, H.2.2, H'.2.2])
    exact MulAction.mem_orbit_iff.mpr ⟨g, Subtype.ext heq⟩
  · intro hmem
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hmem
    refine ⟨g.1, smul_eq_of_mem_Aut g, fun T hT => ⟨g • T, ?_, ?_⟩⟩
    · exact AddSubgroup.smul_mem_pointwise_smul T g H.1 hT
    · exact (autPt_eq_iff_heq g.1 (smul_eq_of_mem_Aut g) T _).mp rfl

theorem smul_eq_iff_rel {W : WeierstrassCurve K} {N : ℕ} [NeZero N] (g : Aut W) (H H' : CycSub W N) :
    g • H = H' ↔ ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun g.1 W.toAffine T) T' := by
  constructor
  · rintro rfl T hT
    refine ⟨g • T, ?_, ?_⟩
    · exact AddSubgroup.smul_mem_pointwise_smul T g H.1 hT
    · exact (autPt_eq_iff_heq g.1 (smul_eq_of_mem_Aut g) T _).mp rfl
  · intro h
    have hle : (g • H.1 : AddSubgroup W.toAffine.Point) ≤ H'.1 := by
      intro P hP
      obtain ⟨T, hT, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists P g H.1).mp hP
      obtain ⟨T', hT', hh⟩ := h T hT
      have : g • T = T' := (autPt_eq_iff_heq g.1 (smul_eq_of_mem_Aut g) T T').mpr hh
      rwa [this]
    haveI : Finite H'.1 := Nat.finite_of_card_ne_zero (by rw [H'.2.2]; exact NeZero.ne N)
    have heq : (g • H.1 : AddSubgroup W.toAffine.Point) = H'.1 :=
      AddSubgroup.eq_of_le_of_card_ge hle (by rw [natCard_smul_addSubgroup, H.2.2, H'.2.2])
    exact Subtype.ext heq

theorem natCard_stab_rel {W : WeierstrassCurve K} {N : ℕ} [NeZero N] (H : CycSub W N) :
    Nat.card {γ : VariableChange K // γ • W = W ∧
        ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ W.toAffine T) T'}
      = Nat.card (MulAction.stabilizer (Aut W) H) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨⟨γ.1, MulAction.mem_stabilizer_iff.mpr γ.2.1⟩,
        MulAction.mem_stabilizer_iff.mpr ((smul_eq_iff_rel _ H H).mpr γ.2.2)⟩
      invFun := fun g => ⟨g.1.1, smul_eq_of_mem_Aut g.1,
        (smul_eq_iff_rel g.1 H H).mp (MulAction.mem_stabilizer_iff.mp g.2)⟩
      left_inv := fun γ => rfl
      right_inv := fun g => rfl }

theorem natCard_fibre_mul_natCard_stabilizer {W : WeierstrassCurve K} {N : ℕ} [NeZero N] {α : Type*}
    (f : CycSub W N → α)
    (hf : ∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • W = W ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T')
    (H : CycSub W N) :
    Nat.card {H' : CycSub W N // f H' = f H} * Nat.card (MulAction.stabilizer (Aut W) H)
      = Nat.card (Aut W) := by
  have e : {H' : CycSub W N // f H' = f H} ≃ MulAction.orbit (Aut W) H :=
    Equiv.subtypeEquivRight (fun H' => by
      rw [eq_comm, hf H H', rel_iff_mem_orbit H H']
      try rfl)
  rw [Nat.card_congr e]
  have hidx : (MulAction.stabilizer (Aut W) H).index = Nat.card (MulAction.orbit (Aut W) H) := by
    rw [MulAction.index_stabilizer]; rfl
  rw [← hidx]
  exact Subgroup.index_mul_card _

theorem natCard_orbit_mul_natCard_stab_param {W : WeierstrassCurve K} {N : ℕ} [NeZero N]
    {ι : Type*} (p : ι → Prop) (φ : ι → W.toAffine.Point) (K' : CycSub W N)
    (hsub : ∀ i, p i → φ i ∈ K'.1) (hsur : ∀ T ∈ K'.1, ∃ i, p i ∧ φ i = T) :
    Nat.card {H'' : CycSub W N // ∃ γ : VariableChange K, γ • W = W ∧
        ∀ i, p i → ∃ T' ∈ H''.1, HEq (Point.vcInvFun γ W.toAffine (φ i)) T'}
      * Nat.card {γ : VariableChange K // γ • W = W ∧
        ∀ i, p i → ∃ i', p i' ∧ HEq (Point.vcInvFun γ W.toAffine (φ i)) (φ i')}
      = Nat.card (Aut W) := by

  have h1 : ∀ γ : VariableChange K, ∀ H'' : CycSub W N,
      (∀ i, p i → ∃ T' ∈ H''.1, HEq (Point.vcInvFun γ W.toAffine (φ i)) T') ↔
        (∀ T ∈ K'.1, ∃ T' ∈ H''.1, HEq (Point.vcInvFun γ W.toAffine T) T') := by
    intro γ H''
    constructor
    · intro h T hT
      obtain ⟨i, hi, rfl⟩ := hsur T hT
      exact h i hi
    · intro h i hi
      exact h (φ i) (hsub i hi)
  have h2 : ∀ γ : VariableChange K,
      (∀ i, p i → ∃ i', p i' ∧ HEq (Point.vcInvFun γ W.toAffine (φ i)) (φ i')) ↔
        (∀ T ∈ K'.1, ∃ T' ∈ K'.1, HEq (Point.vcInvFun γ W.toAffine T) T') := by
    intro γ
    constructor
    · intro h T hT
      obtain ⟨i, hi, rfl⟩ := hsur T hT
      obtain ⟨i', hi', hh⟩ := h i hi
      exact ⟨φ i', hsub i' hi', hh⟩
    · intro h i hi
      obtain ⟨T', hT', hh⟩ := h (φ i) (hsub i hi)
      obtain ⟨i', hi', rfl⟩ := hsur T' hT'
      exact ⟨i', hi', hh⟩
  have eO : {H'' : CycSub W N // ∃ γ : VariableChange K, γ • W = W ∧
        ∀ i, p i → ∃ T' ∈ H''.1, HEq (Point.vcInvFun γ W.toAffine (φ i)) T'}
      ≃ MulAction.orbit (Aut W) K' :=
    Equiv.subtypeEquivRight (fun H'' => by
      rw [← rel_iff_mem_orbit K' H'']
      exact exists_congr fun γ => and_congr_right fun _ => h1 γ H'')
  have eS : {γ : VariableChange K // γ • W = W ∧
        ∀ i, p i → ∃ i', p i' ∧ HEq (Point.vcInvFun γ W.toAffine (φ i)) (φ i')}
      ≃ {γ : VariableChange K // γ • W = W ∧
        ∀ T ∈ K'.1, ∃ T' ∈ K'.1, HEq (Point.vcInvFun γ W.toAffine T) T'} :=
    Equiv.subtypeEquivRight (fun γ => and_congr_right fun _ => h2 γ)
  rw [Nat.card_congr eO, Nat.card_congr eS, natCard_stab_rel K']
  have hidx : (MulAction.stabilizer (Aut W) K').index = Nat.card (MulAction.orbit (Aut W) K') := by
    rw [MulAction.index_stabilizer]; rfl
  rw [← hidx]
  exact Subgroup.index_mul_card _

def cycSubOfGenerator {W : WeierstrassCurve K} {N : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    CycSub W N :=
  ⟨AddSubgroup.zmultiples Q, ⟨inferInstance, by rw [Nat.card_zmultiples, hQ]⟩⟩

private theorem _root_.WInvOrb.exists_generator {W : WeierstrassCurve K} {N : ℕ} [NeZero N] (H : CycSub W N) :
    ∃ Q : W.toAffine.Point, H.1 = AddSubgroup.zmultiples Q ∧ addOrderOf Q = N := by
  haveI := H.2.1
  haveI : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [H.2.2]; exact NeZero.ne N)
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_ofOrder_eq_natCard (α := H.1)
  have hord : addOrderOf (g : W.toAffine.Point) = N := by
    rw [AddSubgroup.addOrderOf_coe, hg, H.2.2]
  refine ⟨g, ?_, hord⟩
  symm
  apply AddSubgroup.eq_of_le_of_card_ge
  · exact AddSubgroup.zmultiples_le_of_mem g.2
  · rw [Nat.card_zmultiples, hord, H.2.2]

p2m_export "WInvOrb" "exists_generator"
end WInvOrb
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"

namespace WInvAuxB

theorem natCard_subgroup_stabilizer_pos {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (S : Subgroup (MulAction.stabilizer (WeierstrassCurve.VariableChange K) W)) : 0 < Nat.card S := by
  haveI := WeierstrassCurve.finite_stabilizer_variableChange K W
  exact Nat.card_pos

end WInvAuxB
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"

namespace P2McuspB

p2m_open "AlgebraicCurve ModularCurve~CycSub"

theorem exists_bezout_of_addOrderOf_eq {N : ℕ} [NeZero N] (a b : ZMod N) (hv : addOrderOf ((a, b) : ZMod N × ZMod N) = N) :
    ∃ x y : ZMod N, x * a + y * b = 1 := by

  set d := Nat.gcd (Nat.gcd a.val b.val) N with hd
  have hdN : d ∣ N := Nat.gcd_dvd_right _ _
  have hda : d ∣ a.val := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hdb : d ∣ b.val := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun h => by
    rw [h] at hdN; exact NeZero.ne N (zero_dvd_iff.mp hdN)
  have hkill : (N / d) • ((a, b) : ZMod N × ZMod N) = 0 := by
    obtain ⟨a', ha'⟩ := hda; obtain ⟨b', hb'⟩ := hdb; obtain ⟨n', hn'⟩ := hdN
    have hNd : N / d = n' := by rw [hn', Nat.mul_div_cancel_left _ hdpos]
    ext
    · show (N / d) • a = 0
      rw [← ZMod.natCast_zmod_val a, ha', hNd, nsmul_eq_mul, ← Nat.cast_mul,
        show n' * (d * a') = N * a' by rw [hn']; ring, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    · show (N / d) • b = 0
      rw [← ZMod.natCast_zmod_val b, hb', hNd, nsmul_eq_mul, ← Nat.cast_mul,
        show n' * (d * b') = N * b' by rw [hn']; ring, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hdvd : N ∣ N / d := by
    have := addOrderOf_dvd_of_nsmul_eq_zero hkill
    rwa [hv] at this
  have hd1 : d = 1 := by
    obtain ⟨n', hn'⟩ := hdN
    have hNd : N / d = n' := by rw [hn', Nat.mul_div_cancel_left _ hdpos]
    rw [hNd] at hdvd
    have hn'pos : 0 < n' := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hn'; exact NeZero.ne N hn'
    have := Nat.le_of_dvd hn'pos hdvd
    rw [hn'] at this
    nlinarith

  have h1 : (Nat.gcd (Nat.gcd a.val b.val) N : ℤ) = 1 := by rw [← hd, hd1]; rfl
  have hg1 := Nat.gcd_eq_gcd_ab (Nat.gcd a.val b.val) N
  have hg2 := Nat.gcd_eq_gcd_ab a.val b.val
  set g := Nat.gcd a.val b.val
  refine ⟨((Nat.gcdA a.val b.val * Nat.gcdA g N : ℤ) : ZMod N), ((Nat.gcdB a.val b.val * Nat.gcdA g N : ℤ) : ZMod N), ?_⟩
  have key : ((a.val : ℤ) * Nat.gcdA a.val b.val + (b.val : ℤ) * Nat.gcdB a.val b.val) * Nat.gcdA g N
      + (N : ℤ) * Nat.gcdB g N = 1 := by
    rw [← hg2, ← h1, hg1]
  have := congrArg (fun z : ℤ => (z : ZMod N)) key
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero,
    Int.cast_one, ZMod.natCast_zmod_val] at this
  rw [← this]; push_cast; ring

theorem exists_compl_of_addOrderOf_eq {N : ℕ} [NeZero N] (v : ZMod N × ZMod N) (hv : addOrderOf v = N) :
    ∃ w : ZMod N × ZMod N, Function.Bijective (fun p : ZMod N × ZMod N => p.1 • v + p.2 • w) := by
  obtain ⟨a, b⟩ := v
  obtain ⟨x, y, hxy⟩ := exists_bezout_of_addOrderOf_eq a b hv
  refine ⟨(-y, x), Function.bijective_iff_has_inverse.mpr ⟨fun q => (x * q.1 + y * q.2, -b * q.1 + a * q.2), ?_, ?_⟩⟩
  · intro p
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_
    · show x * (p.1 * a + p.2 * -y) + y * (p.1 * b + p.2 * x) = p.1
      linear_combination (p.1) * hxy
    · show -b * (p.1 * a + p.2 * -y) + a * (p.1 * b + p.2 * x) = p.2
      linear_combination (p.2) * hxy
  · intro q
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_
    · show (x * q.1 + y * q.2) * a + (-b * q.1 + a * q.2) * -y = q.1
      linear_combination (q.1) * hxy
    · show (x * q.1 + y * q.2) * b + (-b * q.1 + a * q.2) * x = q.2
      linear_combination (q.2) * hxy

open WeierstrassCurve WeierstrassCurve.Affine in

theorem exists_generator_image_torsion
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    {V : Type*} [AddCommGroup V] (φ : W.toAffine.Point →+ V) (hφker : φ.ker = AddSubgroup.zmultiples Q) :
    ∃ Q' : V, addOrderOf Q' = N ∧
      (∀ P : W.toAffine.Point, N • P = 0 → φ P ∈ AddSubgroup.zmultiples Q') ∧
      (∀ T ∈ AddSubgroup.zmultiples Q', ∃ P : W.toAffine.Point, N • P = 0 ∧ φ P = T) := by
  classical
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (F := K) (K := K) W hN
  have hb : (W⁄K) = W.toAffine := by
    show (W.baseChange K).toAffine = W.toAffine
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hb] at eT

  have hmem : ∀ P : W.toAffine.Point, P ∈ Submodule.torsionBy ℤ W.toAffine.Point N ↔ N • P = 0 := by
    intro P; rw [Submodule.mem_torsionBy_iff]; show ((N : ℤ) • P = 0) ↔ N • P = 0; rw [natCast_zsmul]
  have hQN : N • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  set v : ZMod N × ZMod N := eT.symm ⟨Q, (hmem Q).mpr hQN⟩ with hv_def
  have hv : addOrderOf v = N := by
    rw [hv_def, AddEquiv.addOrderOf_eq]
    have := addOrderOf_injective (Submodule.torsionBy ℤ W.toAffine.Point N).subtype.toAddMonoidHom
      Subtype.val_injective ⟨Q, (hmem Q).mpr hQN⟩

    exact this.symm.trans hQ
  obtain ⟨w, hbij⟩ := exists_compl_of_addOrderOf_eq v hv

  have hsm : ∀ (c : ZMod N) (z : ZMod N × ZMod N), eT (c • z) = c.val • eT z := by
    intro c z
    rw [← map_nsmul]; congr 1
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    ext <;> simp [nsmul_eq_mul]

  have hzmod : ∀ (z : ℤ) (P : W.toAffine.Point), N • P = 0 → z • P = ((z : ZMod N).val) • P := by
    intro z P hP
    have h1 : (((z : ZMod N).val : ℕ) : ℤ) = z % N := ZMod.val_intCast z
    conv_lhs => rw [← Int.emod_add_mul_ediv z N, add_zsmul, mul_comm, mul_zsmul, natCast_zsmul, hP,
      zsmul_zero, add_zero, ← h1, natCast_zsmul]
  have hQker : φ Q = 0 := by rw [← AddMonoidHom.mem_ker, hφker]; exact AddSubgroup.mem_zmultiples Q

  set R : W.toAffine.Point := (eT w).1 with hR
  have hRN : N • R = 0 := (hmem R).mp (eT w).2
  have hRsub : ∀ m : ℕ, ((m • eT w : Submodule.torsionBy ℤ W.toAffine.Point N) : W.toAffine.Point) = m • R := by
    intro m; rw [hR]; rfl
  have hQsub : ∀ m : ℕ, ((m • eT v : Submodule.torsionBy ℤ W.toAffine.Point N) : W.toAffine.Point) = m • Q := by
    intro m; rw [hv_def, AddEquiv.apply_symm_apply]; rfl
  refine ⟨φ R, ?_, ?_, ?_⟩
  ·
    apply Nat.dvd_antisymm
    · exact addOrderOf_dvd_of_nsmul_eq_zero (by rw [← map_nsmul, hRN, map_zero])
    · have key : ∀ m : ℕ, m • φ R = 0 → N ∣ m := by
        intro m hm
        rw [← map_nsmul, ← AddMonoidHom.mem_ker, hφker, AddSubgroup.mem_zmultiples_iff] at hm
        obtain ⟨z, hz⟩ := hm
        rw [hzmod z Q hQN] at hz

        set c : ZMod N := (z : ZMod N)
        have h2 : eT (c • v) = eT ((m : ZMod N) • w) := by
          apply Subtype.ext
          rw [hsm, hsm, hQsub, hRsub, hz, ZMod.val_natCast]

          exact nsmul_eq_mod_nsmul m hRN
        have h3 : c • v = (m : ZMod N) • w := eT.injective h2
        have h4 : (fun p : ZMod N × ZMod N => p.1 • v + p.2 • w) (c, -(m : ZMod N))
            = (fun p : ZMod N × ZMod N => p.1 • v + p.2 • w) (0, 0) := by
          simp only [zero_smul, add_zero, neg_smul, h3]; exact add_neg_cancel _
        have h5 := hbij.1 h4
        simp only [Prod.mk.injEq, neg_eq_zero] at h5
        exact (ZMod.natCast_eq_zero_iff m N).mp h5.2
      exact key _ (addOrderOf_nsmul_eq_zero _)
  ·
    intro P hP
    obtain ⟨p, hp⟩ := hbij.2 (eT.symm ⟨P, (hmem P).mpr hP⟩)
    have h1 := congrArg (fun z => ((eT z : Submodule.torsionBy ℤ W.toAffine.Point N) : W.toAffine.Point)) hp
    simp only [map_add, AddEquiv.apply_symm_apply, Submodule.coe_add] at h1
    rw [hsm, hsm, hQsub, hRsub] at h1

    rw [← h1, map_add, map_nsmul, map_nsmul, hQker, nsmul_zero, zero_add]
    exact (AddSubgroup.zmultiples (φ R)).nsmul_mem (AddSubgroup.mem_zmultiples _) _
  ·
    intro T hT
    obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
    refine ⟨z • R, ?_, by rw [map_zsmul]⟩
    rw [smul_comm, hRN, zsmul_zero]

section GenIndep

variable {K : Type*} [Field K] [DecidableEq K]

theorem exists_eq_nsmul_of_mem_zmultiples' {A : Type*} [AddCommGroup A] {Q : A} {N : ℕ}
    (hQ : addOrderOf Q = N) (hN : 0 < N) {T : A} (hT : T ∈ AddSubgroup.zmultiples Q) (hT0 : T ≠ 0) :
    ∃ k, 1 ≤ k ∧ k ≤ N - 1 ∧ k • Q = T := by
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
  have hper : ∀ w : ℤ, w • Q = (w % N) • Q := fun w => by
    conv_lhs => rw [← Int.emod_add_mul_ediv w N, add_zsmul, mul_comm, mul_zsmul, natCast_zsmul]
    rw [← hQ, addOrderOf_nsmul_eq_zero, zsmul_zero, add_zero]
  set k := (z % N).toNat with hk
  have hz : z % N = (k : ℤ) := (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))).symm
  have hkQ : z • Q = k • Q := by rw [hper z, hz, natCast_zsmul]
  refine ⟨k, ?_, ?_, hkQ.symm⟩
  · by_contra h
    have : k = 0 := by omega
    rw [hkQ, this, zero_nsmul] at hT0; exact hT0 rfl
  · have : (k : ℤ) < N := hz ▸ Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    omega

theorem nsmul_ne_zero' {A : Type*} [AddMonoid A] {Q : A} {N : ℕ} (hQ : addOrderOf Q = N)
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N - 1) : k • Q ≠ 0 := by
  intro h
  have := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
  rw [hQ] at this
  exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

theorem oddOrderSummingSet_eq_of_zmultiples_eq (W : WeierstrassCurve K) {N : ℕ} (hN : 0 < N)
    {Q Q' : W.toAffine.Point} (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N)
    (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.oddOrderSummingSet Q (N - 1) = W.oddOrderSummingSet Q' (N - 1) := by
  have key : ∀ {Q Q' : W.toAffine.Point}, addOrderOf Q = N → addOrderOf Q' = N →
      AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' →
      W.oddOrderSummingSet Q (N - 1) ⊆ W.oddOrderSummingSet Q' (N - 1) := by
    intro Q Q' hQ hQ' h P hP
    rw [mem_oddOrderSummingSet] at hP ⊢
    obtain ⟨k, hk1, hkN, rfl⟩ := hP
    have hmem : k • Q ∈ AddSubgroup.zmultiples Q' :=
      h ▸ (AddSubgroup.zmultiples Q).nsmul_mem (AddSubgroup.mem_zmultiples Q) k
    obtain ⟨m, hm1, hmN, hm⟩ := exists_eq_nsmul_of_mem_zmultiples' hQ' hN hmem (nsmul_ne_zero' hQ hk1 hkN)
    exact ⟨m, hm1, hmN, by rw [hm]⟩
  exact Finset.Subset.antisymm (key hQ hQ' h) (key hQ' hQ h.symm)

theorem fullKernelQuotient_eq_of_zmultiples_eq (W : WeierstrassCurve K) {N : ℕ} (hN : 0 < N)
    {Q Q' : W.toAffine.Point} (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N)
    (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.fullKernelQuotient Q N = W.fullKernelQuotient Q' N := by
  unfold fullKernelQuotient
  rw [oddOrderSummingSet_eq_of_zmultiples_eq W hN hQ hQ' h]

theorem j_congr {V V' : WeierstrassCurve K} (h : V = V') (hV : V.IsElliptic) (hV' : V'.IsElliptic) :
    @WeierstrassCurve.j K _ V hV = @WeierstrassCurve.j K _ V' hV' := by
  subst h; rfl

end GenIndep
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"

section Transport

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def placeCongr {E₁ E₂ : IntermediateField K L} (h : E₁ = E₂) : Place K ↥E₁ ≃ Place K ↥E₂ := by
  subst h; exact Equiv.refl _

theorem placeCongr_symm_isRational {E₁ E₂ : IntermediateField K L} (h : E₁ = E₂) (P : Place K ↥E₂) :
    ((placeCongr h).symm P).IsRational ↔ P.IsRational := by
  subst h; rfl

theorem placeCongr_symm_mem {E₁ E₂ : IntermediateField K L} (h : E₁ = E₂) (P : Place K ↥E₂) (x : ↥E₁) (y : ↥E₂)
    (hxy : (x : L) = (y : L)) : x ∈ ((placeCongr h).symm P).toValuationSubring ↔ y ∈ P.toValuationSubring := by
  subst h
  obtain rfl : x = y := Subtype.ext hxy
  rfl

end Transport
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"

section LevelN

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem isRational_C [IsAlgClosed K] (x : Place K ↥(modularFunctionFieldC K N)) : x.IsRational :=
  (Place.isRational_iff_deg_eq_one x).mpr (place_deg_eq_one_of_isAlgClosed K N x)

theorem isIntegral_jNGeomGen :
    IsIntegral (Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) (jNGeomGen K N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  set A := Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)) with hA
  have hjA : jGeomGen K N ∈ A := Algebra.subset_adjoin rfl
  let g : Polynomial ℤ →+* ↥A := Polynomial.eval₂RingHom (Int.castRingHom ↥A) ⟨jGeomGen K N, hjA⟩
  have hg : (algebraMap ↥A ↥(modularFunctionFieldC K N)).comp g
      = Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC K N)) (jGeomGen K N) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [g]
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
  rw [Polynomial.eval₂_map, hg]
  exact evalModularPair_jGeomGen_eq_zero K N data

theorem jNGeomGen_mem_of_jGeomGen_mem (x : Place K ↥(modularFunctionFieldC K N))
    (hj : jGeomGen K N ∈ x.toValuationSubring) : jNGeomGen K N ∈ x.toValuationSubring :=
  x.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_jNGeomGen K N)

variable {K N} in
theorem isRational_full [IsAlgClosed K] (hCF : modularFunctionFieldC K N = modularFunctionFieldFullC K N)
    (P : Place K ↥(modularFunctionFieldFullC K N)) : P.IsRational :=
  (placeCongr_symm_isRational hCF P).mp (isRational_C K N _)

variable {K N} in
theorem jNF_mem_of_jF_mem (hCF : modularFunctionFieldC K N = modularFunctionFieldFullC K N)
    (P : Place K ↥(modularFunctionFieldFullC K N))
    (h : (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) ∈ P.toValuationSubring) :
    (⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ : ↥(modularFunctionFieldFullC K N)) ∈ P.toValuationSubring := by
  have h1 := (placeCongr_symm_mem hCF P (jGeomGen K N) ⟨jqModC K, jqModC_mem_full K N⟩ rfl).mpr h
  exact (placeCongr_symm_mem hCF P (jNGeomGen K N) ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ rfl).mp
    (jNGeomGen_mem_of_jGeomGen_mem K N _ h1)

end LevelN
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"

section Along

variable {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M]

theorem evalAt_restrictAlong (ψ : F →ₐ[K] M) (hψ : ψ.toRingHom.IsIntegral) (W₀ : Place K M)
    (hrat : (W₀.restrictAlong ψ hψ).IsRational) {g : F} (hg : g ∈ (W₀.restrictAlong ψ hψ).toValuationSubring) :
    (W₀.restrictAlong ψ hψ).evalAt g = W₀.evalAt (ψ g) := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI := isIntegral_along ψ hψ
  exact (Place.evalAt_algebraMap_eq_evalAt_restrict (F := F) W₀ hrat hg).symm

theorem ramificationIndexAlong_pos (ψ : F →ₐ[K] M) (hψ : ψ.toRingHom.IsIntegral) (W₀ : Place K M) :
    0 < Place.ramificationIndexAlong ψ W₀ := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI := isIntegral_along ψ hψ
  exact W₀.ramificationIndex_pos (F := F)

theorem mem_of_ord_sub_algebraMap_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (x : F) (c : K)
    (h : 0 < v.ord (x - algebraMap K F c)) : x ∈ v.toValuationSubring := by
  have hne : x - algebraMap K F c ≠ 0 := fun h0 => by rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : x - algebraMap K F c ∈ v.toValuationSubring := (v.mem_iff_ord_nonneg hne).mpr h.le
  have := add_mem hmem (v.algebraMap_mem' c)
  rwa [sub_add_cancel] at this

end Along
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"

end P2McuspB
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"

namespace P2MKcA
namespace DAssembly

end P2MKcA.DAssembly
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.P2MKcA.DAssembly P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard.WInvOrb"

open P2MKcA.DAssembly in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (j₀ : K) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀)
    (S : Finset (Place K (modularFunctionFieldFullC K N)))
    (hS : ∀ P, P ∈ S ↔
      0 < P.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
        algebraMap K (modularFunctionFieldFullC K N) j₀)) :
    ∃ f : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
        Place K (modularFunctionFieldFullC K N),
      (∀ H, f H ∈ S) ∧ (∀ P ∈ S, ∃ H, f H = P) ∧
      (∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ∧
      (∀ H, (f H).ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
          algebraMap K (modularFunctionFieldFullC K N) j₀) =
        (Nat.card {H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
          f H' = f H} : ℤ)) ∧

      (∀ (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N})
          (Q : E₀.toAffine.Point), H.1 = AddSubgroup.zmultiples Q → addOrderOf Q = N →
          ∀ hΔ : (E₀.fullKernelQuotient Q N).Δ ≠ 0,
          (f H).evalAt (⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ :
              modularFunctionFieldFullC K N)
            = @WeierstrassCurve.j K _ (E₀.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) ∧

      (∀ (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N})
          (Q : E₀.toAffine.Point), H.1 = AddSubgroup.zmultiples Q → addOrderOf Q = N →
          ∀ (hΔ : (E₀.fullKernelQuotient Q N).Δ ≠ 0)
            (φ : E₀.toAffine.Point →+ (E₀.fullKernelQuotient Q N).toAffine.Point),
            φ.ker = AddSubgroup.zmultiples Q →
            (∀ P : E₀.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
              (φ P).coordsOrZero =
                (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
                    ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
                 P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
                    ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) →
              (f H).ord ((⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ :
                    modularFunctionFieldFullC K N) -
                  algebraMap K (modularFunctionFieldFullC K N)
                    (@WeierstrassCurve.j K _ (E₀.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩)) =
                (Nat.card {H'' : {H'' : AddSubgroup (E₀.fullKernelQuotient Q N).toAffine.Point //
                      IsAddCyclic H'' ∧ Nat.card H'' = N} //
                    ∃ γ : VariableChange K, γ • (E₀.fullKernelQuotient Q N) = E₀.fullKernelQuotient Q N ∧
                      ∀ P : E₀.toAffine.Point, N • P = 0 → ∃ T' ∈ H''.1,
                        HEq (Point.vcInvFun γ (E₀.fullKernelQuotient Q N).toAffine (φ P)) T'} : ℤ)) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  let F := modularFunctionFieldFullC K N
  let jF : F := ⟨jqModC K, jqModC_mem_full K N⟩
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)

  obtain ⟨M, _iF, _iD, _iA, t, ht, hfin, hgal, W₀, hW₀, θ, ρ, hfull, hθinj, hρE, -, hequivC,
    hsurjC, -, hVR, hVRstar⟩ :=
    ModularCurve.exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard
      K p N hN j₀ E₀ hE₀
  haveI := hfin
  haveI := hgal

  let tk : K⟮t⟯ := ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩
  let E : WeierstrassCurve K⟮t⟯ := WeierstrassCurve.ofJ tk
  have hEj : E.j = tk := WeierstrassCurve.ofJ_j tk
  have hjt : algebraMap K⟮t⟯ M E.j = t := by rw [hEj]; rfl
  have hEtr : Transcendental K E.j := by
    rw [hEj]
    intro halg
    exact ht (by simpa using halg.algebraMap (A := M))

  obtain ⟨Φ, hnatA, hSC⟩ :=
    ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
      K N hN K⟮t⟯ M E hEtr hfull

  let X : Type _ := {ψ : F →ₐ[K] M // ψ jF = t}
  let embX : {ψ : F →ₐ[K] M // ψ jF = algebraMap K⟮t⟯ M E.j} ≃ X :=
    Equiv.subtypeEquivRight (fun ψ => by rw [hjt])
  let ΦX : CycSub (E.baseChange M).toAffine.Point N ≃ X := Φ.trans embX
  have ΦX_val : ∀ H, (ΦX H).1 = (Φ H).1 := fun H => rfl

  have hint : ∀ ψ : F →ₐ[K] M, ψ jF = t → ψ.toRingHom.IsIntegral :=
    fun ψ hψ => isIntegral_of_apply_eq jF t ψ hψ

  obtain ⟨hcard₀, g₀, hg₀⟩ := tors_facts E₀ hN
  have hθ : Set.InjOn θ (tors (E.baseChange M).toAffine.Point N) := by
    intro P hP Q hQ h
    have hPQ : N • (P - Q) = 0 := by
      rw [nsmul_sub, show N • P = 0 from hP, show N • Q = 0 from hQ, sub_zero]
    have := hθinj N (P - Q) hpN hPQ (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp this
  have hθs : ∀ y ∈ tors E₀.toAffine.Point N, ∃ x ∈ tors (E.baseChange M).toAffine.Point N, θ x = y := by
    let θr : tors (E.baseChange M).toAffine.Point N → tors E₀.toAffine.Point N :=
      fun P => ⟨θ P.1, show N • θ P.1 = 0 by rw [← map_nsmul, show N • P.1 = 0 from P.2, map_zero]⟩
    have hinj : Function.Injective θr := fun P Q h =>
      Subtype.ext (hθ P.2 Q.2 (congrArg Subtype.val h))
    haveI : Finite (tors E₀.toAffine.Point N) :=
      Nat.finite_of_card_ne_zero (by rw [hcard₀]; exact pow_ne_zero 2 hN0)
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [hcard₀]
      exact le_of_eq hfull.symm)
    intro y hy
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

  obtain ⟨H₁, -⟩ := mapCyc_surjective hN0 hθ hθs (cycOf g₀ hg₀)
  let ι : F →ₐ[K] M := (ΦX H₁).1
  have hι : ι jF = t := (ΦX H₁).2

  obtain ⟨-, hBi, hBii, hBiii, hBiv⟩ :=
    AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K jF t j₀ ι hι hfin hgal
      hint W₀ hW₀

  let D : (M ≃ₐ[K⟮t⟯] M) → Prop := fun σ => SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀
  let act : (M ≃ₐ[K⟮t⟯] M) → ((E.baseChange M).toAffine.Point →+ (E.baseChange M).toAffine.Point) :=
    fun σ => WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M)
  have hact : ∀ σ, Function.Injective (act σ) := fun σ =>
    WeierstrassCurve.Affine.Point.map_injective (W' := E) (σ : M →ₐ[K⟮t⟯] M)
  have hσt : ∀ σ : M ≃ₐ[K⟮t⟯] M, σ t = t := fun σ => σ.commutes tk
  let actX : (M ≃ₐ[K⟮t⟯] M) → X → X := fun σ ψ =>
    ⟨((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ.1, by
      show σ (ψ.1 jF) = t
      rw [ψ.2, hσt]⟩
  have hnat : ∀ σ (H : CycSub (E.baseChange M).toAffine.Point N),
      ΦX (mapCyc (act σ) H (hact σ).injOn) = actX σ (ΦX H) := by
    intro σ H
    apply Subtype.ext
    rw [ΦX_val]
    exact hnatA σ H (mapCyc (act σ) H (hact σ).injOn) rfl

  have hequiv : ∀ σ (hσ : D σ) (P : (E.baseChange M).toAffine.Point),
      θ (act σ P) = autPt (ρ σ) (hρE σ hσ) (θ P) :=
    fun σ hσ P => ((autPt_eq_iff_heq _ _ _ _).mpr (hequivC σ hσ P)).symm
  have hsurj : ∀ (γ : VariableChange K) (hγ : γ • E₀ = E₀), ∃ σ, D σ ∧
      ((∀ P, θ (act σ P) = autPt γ hγ (θ P)) ∨ (∀ P, θ (act σ P) = -autPt γ hγ (θ P))) := by
    intro γ hγ
    obtain ⟨σ, hσ, h⟩ := hsurjC γ hγ
    refine ⟨σ, hσ, ?_⟩
    rcases h with h | h
    · exact Or.inl fun P => ((autPt_eq_iff_heq _ _ _ _).mpr (h P)).symm
    · refine Or.inr fun P => ?_
      have := (autPt_eq_iff_heq γ hγ (θ P) _).mpr (h P)
      rw [this, neg_neg]

  let π : X → Place K F := fun ψ => W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2)
  have hπS : ∀ ψ, π ψ ∈ S := fun ψ => (hS _).mpr (hBi ψ.1 ψ.2)
  have hπsurj : ∀ P ∈ S, ∃ ψ, π ψ = P := by
    intro P hP
    obtain ⟨ψ, hψ, h⟩ := hBii P ((hS P).mp hP)
    exact ⟨⟨ψ, hψ⟩, h⟩
  have hπfib : ∀ ψ ψ' : X, π ψ = π ψ' ↔ ∃ σ, D σ ∧ ψ' = actX σ ψ := by
    intro ψ ψ'
    rw [show (π ψ = π ψ') = (W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2) =
      W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2)) from rfl, hBiii ψ.1 ψ'.1 ψ.2 ψ'.2]
    refine exists_congr fun σ => and_congr_right fun _ => ?_
    rw [Subtype.ext_iff]
  let e : Place K F → ℤ := fun P => P.ord (jF - algebraMap K F j₀)
  have hπe : ∀ ψ : X, e (π ψ) = Nat.card {ψ' // π ψ' = π ψ} := fun ψ => hBiv ψ.1 ψ.2

  obtain ⟨Ξ, ε, Ξ_val, hε, hfS, hfsurj, hfib, hord⟩ := assemble hN0 θ hθ hθs D act hact ρ hρE hequiv hsurj ΦX actX
    hnat π S hπS hπsurj hπfib e hπe

  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hNM : (N : M) ≠ 0 := fun h => hN (by
    have : algebraMap K M (N : K) = algebraMap K M 0 := by rw [map_natCast, map_zero, h]
    exact (algebraMap K M).injective this)
  have hCF : modularFunctionFieldC K N = F := modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN
  haveI instEM : (E.baseChange M).IsElliptic := (inferInstance : (E.map (algebraMap K⟮t⟯ M)).IsElliptic)
  let jNF : F := ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩
  have hεH : ∀ H₀, ε H₀ = ΦX (Ξ.symm H₀) := fun H₀ => by rw [hε]; rfl
  have hratF : ∀ P : Place K F, P.IsRational := fun P => P2McuspB.isRational_full hCF P
  have hjNmem : ∀ H₀, jNF ∈ (π (ε H₀)).toValuationSubring := fun H₀ =>
    P2McuspB.jNF_mem_of_jF_mem hCF _
      (P2McuspB.mem_of_ord_sub_algebraMap_pos _ jF j₀ ((hS _).mp (hfS H₀)))

  have gen : ∀ H₀ : CycSub E₀.toAffine.Point N, ∃ QM : (E.baseChange M).toAffine.Point,
      addOrderOf QM = N ∧ (Ξ.symm H₀).1 = AddSubgroup.zmultiples QM ∧
      AddSubgroup.zmultiples (θ QM) = H₀.1 ∧ addOrderOf (θ QM) = N := by
    intro H₀
    obtain ⟨QM, hQM, hHM⟩ := exists_generator hN0 (Ξ.symm H₀)
    have hθQM : AddSubgroup.zmultiples (θ QM) = H₀.1 := by
      rw [← AddMonoidHom.map_zmultiples, hHM, ← Ξ_val, Equiv.apply_symm_apply]
    refine ⟨QM, hQM, hHM.symm, hθQM, ?_⟩
    have := H₀.2.2
    rwa [← hθQM, Nat.card_zmultiples] at this
  refine ⟨fun H₀ => π (ε H₀), hfS, hfsurj, fun H H' => (hfib H H').trans Iff.rfl, hord, ?_, ?_⟩
  ·
    intro H₀ Q hHQ hQ hΔ
    obtain ⟨QM, hQM, hHM, hθQM, hordθ⟩ := gen H₀
    have hΔM : ((E.baseChange M).fullKernelQuotient QM N).Δ ≠ 0 :=
      WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N (E.baseChange M) hNM QM hQM
    have hΔ₀' : (E₀.fullKernelQuotient (θ QM) N).Δ ≠ 0 :=
      WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N E₀ hN (θ QM) hordθ
    have step1 : (π (ε H₀)).evalAt jNF = W₀.evalAt ((ε H₀).1 jNF) :=
      P2McuspB.evalAt_restrictAlong (ε H₀).1 (hint _ (ε H₀).2) W₀ (hratF _) (hjNmem H₀)
    have step2 : (ε H₀).1 jNF = @WeierstrassCurve.j M _ ((E.baseChange M).fullKernelQuotient QM N)
        ⟨isUnit_iff_ne_zero.mpr hΔM⟩ := by
      rw [hεH, ΦX_val]
      exact hSC (Ξ.symm H₀) QM hHM hQM hΔM
    have step3 := (hVR QM hQM hΔM hΔ₀').2
    have step4 : E₀.fullKernelQuotient (θ QM) N = E₀.fullKernelQuotient Q N :=
      P2McuspB.fullKernelQuotient_eq_of_zmultiples_eq E₀ hNpos hordθ hQ (hθQM.trans hHQ)
    show (π (ε H₀)).evalAt jNF = _
    rw [step1, step2, step3]
    exact P2McuspB.j_congr step4 _ _
  ·
    intro H₀ Q hHQ hQ hΔ φ hφker hφ
    obtain ⟨QM, hQM, hHM, hθQM, hordθ⟩ := gen H₀
    have hΔM : ((E.baseChange M).fullKernelQuotient QM N).Δ ≠ 0 :=
      WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N (E.baseChange M) hNM QM hQM
    have hΔ₀' : (E₀.fullKernelQuotient (θ QM) N).Δ ≠ 0 :=
      WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N E₀ hN (θ QM) hordθ
    letI instW' : (E₀.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    set a' : K := @WeierstrassCurve.j K _ (E₀.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩ with ha'
    set jM : M := @WeierstrassCurve.j M _ ((E.baseChange M).fullKernelQuotient QM N)
        ⟨isUnit_iff_ne_zero.mpr hΔM⟩ with hjM
    have step2 : (ε H₀).1 jNF = jM := by
      rw [hεH, ΦX_val]
      exact hSC (Ξ.symm H₀) QM hHM hQM hΔM
    have step4 : E₀.fullKernelQuotient (θ QM) N = E₀.fullKernelQuotient Q N :=
      P2McuspB.fullKernelQuotient_eq_of_zmultiples_eq E₀ hNpos hordθ hQ (hθQM.trans hHQ)
    have hjK : @WeierstrassCurve.j K _ (E₀.fullKernelQuotient (θ QM) N) ⟨isUnit_iff_ne_zero.mpr hΔ₀'⟩ = a' :=
      P2McuspB.j_congr step4 _ _

    have hstar := hVRstar QM hQM hΔM hΔ₀'
    rw [hjK] at hstar
    rw [step4] at hstar

    set ψ : F →ₐ[K] M := (ε H₀).1 with hψdef
    have hψ : ψ jF = t := (ε H₀).2
    set eψ : ℕ := Place.ramificationIndexAlong ψ W₀ with heψ
    have heψpos : 0 < eψ := P2McuspB.ramificationIndexAlong_pos ψ (hint ψ hψ) W₀
    have hx1 : W₀.ord (t - algebraMap K M j₀) = eψ * (π (ε H₀)).ord (jF - algebraMap K F j₀) := by
      have h1 := Place.ord_restrictAlong ψ (hint ψ hψ) W₀ (jF - algebraMap K F j₀)
      rw [map_sub, hψ, AlgHom.commutes] at h1
      exact h1
    have hx2 : W₀.ord (jM - algebraMap K M a') = eψ * (π (ε H₀)).ord (jNF - algebraMap K F a') := by
      have h1 := Place.ord_restrictAlong ψ (hint ψ hψ) W₀ (jNF - algebraMap K F a')
      rw [map_sub, AlgHom.commutes] at h1
      rw [← step2]
      exact h1

    have hos := WInvOrb.natCard_fibre_mul_natCard_stabilizer (fun H => π (ε H))
      (fun H H' => (hfib H H').trans Iff.rfl) H₀
    obtain ⟨Q', hQ'ord, hQ'sub, hQ'sur⟩ := P2McuspB.exists_generator_image_torsion hN E₀ Q hQ φ hφker
    have hos' := WInvOrb.natCard_orbit_mul_natCard_stab_param (W := E₀.fullKernelQuotient Q N)
      (fun P : E₀.toAffine.Point => N • P = 0) (fun P => φ P) (WInvOrb.cycSubOfGenerator Q' hQ'ord)
      (fun P hP => hQ'sub P hP) (fun T hT => hQ'sur T hT)
    have hstab : Nat.card (MulAction.stabilizer (WInvOrb.Aut E₀) H₀)
        = Nat.card {γ' : VariableChange K // γ' • (E₀.fullKernelQuotient Q N) = E₀.fullKernelQuotient Q N ∧
            ∀ P : E₀.toAffine.Point, N • P = 0 → ∃ P' : E₀.toAffine.Point, N • P' = 0 ∧
              HEq (Point.vcInvFun γ' (E₀.fullKernelQuotient Q N).toAffine (φ P)) (φ P')} := by
      rw [← WInvOrb.natCard_stab_rel H₀]
      have := WeierstrassCurve.natCard_variableChange_stabilizer_eq_of_fullKernelQuotient hN E₀ Q hQ hΔ φ hφker hφ
      rw [← hHQ] at this
      exact this
    have hu : 0 < Nat.card (MulAction.stabilizer (WInvOrb.Aut E₀) H₀) :=
      WInvAuxB.natCard_subgroup_stabilizer_pos E₀ _

    have hr := hord H₀

    set rN : ℤ := (π (ε H₀)).ord (jNF - algebraMap K F a') with hrN
    set r : ℤ := (π (ε H₀)).ord (jF - algebraMap K F j₀) with hr'
    set fib : ℕ := Nat.card {H' // π (ε H') = π (ε H₀)} with hfib'
    set u : ℕ := Nat.card (MulAction.stabilizer (WInvOrb.Aut E₀) H₀) with hu'
    set T : ℕ := Nat.card {H'' : WInvOrb.CycSub (E₀.fullKernelQuotient Q N) N //
        ∃ γ : VariableChange K, γ • (E₀.fullKernelQuotient Q N) = E₀.fullKernelQuotient Q N ∧
          ∀ P : E₀.toAffine.Point, N • P = 0 → ∃ T' ∈ H''.1,
            HEq (Point.vcInvFun γ (E₀.fullKernelQuotient Q N).toAffine (φ P)) T'} with hT'

    have hA : (Nat.card (MulAction.stabilizer (VariableChange K) E₀) : ℤ) = fib * u := by
      have h := hos.symm
      exact_mod_cast h
    have hA' : (Nat.card (MulAction.stabilizer (VariableChange K) (E₀.fullKernelQuotient Q N)) : ℤ) = T * u := by
      rw [← hstab] at hos'
      have h := hos'.symm
      exact_mod_cast h
    rw [hx1, hx2, hA, hA'] at hstar
    have hrfib : r = (fib : ℤ) := hr
    rw [hrfib] at hstar

    have hne : ((eψ : ℤ) * (fib : ℤ) * (u : ℤ)) ≠ 0 := by
      have hfibpos : (0 : ℤ) < fib := by
        rw [← hrfib]
        exact (hS _).mp (hfS H₀)
      have : (0 : ℤ) < eψ := by exact_mod_cast heψpos
      have : (0 : ℤ) < u := by exact_mod_cast hu
      positivity
    show rN = (T : ℤ)
    have key : rN * ((eψ : ℤ) * fib * u) = (T : ℤ) * ((eψ : ℤ) * fib * u) := by
      have := hstar
      push_cast at this ⊢
      linear_combination this
    exact mul_right_cancel₀ hne key

end S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard
end P2MW
export P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard (solution)
