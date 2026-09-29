-- Prove2me | solution 1 for ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/da02f2a2-6b53-5382-95c0-d4f7390c07a5

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_of_transcendental_j
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve
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

abbrev CycSub (A : Type*) [AddCommGroup A] (N : ℕ) : Type _ :=
  {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N}

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
    ∃ f : CycSub E₀.toAffine.Point N → Pl,
      (∀ H, f H ∈ S) ∧ (∀ P ∈ S, ∃ H, f H = P) ∧
      (∀ H H', f H = f H' ↔ Rel E₀ N H H') ∧
      ∀ H, e (f H) = Nat.card {H' // f H' = f H} := by
  classical

  let Ξf : CycSub Pt N → CycSub E₀.toAffine.Point N := fun H => mapCyc θ H (injOn_of_injOn_tors hθ H)
  have hΞ : Function.Bijective Ξf :=
    ⟨fun H H' h => mapCyc_injective hθ h, fun H₀ => mapCyc_surjective hN hθ hθs H₀⟩
  let Ξ : CycSub Pt N ≃ CycSub E₀.toAffine.Point N := Equiv.ofBijective Ξf hΞ
  have Ξ_val : ∀ H, (Ξ H).1 = H.1.map θ := fun H => rfl

  let ε : CycSub E₀.toAffine.Point N ≃ X := Ξ.symm.trans Φ
  refine ⟨fun H₀ => π (ε H₀), fun H₀ => hπS _, ?_, ?_, ?_⟩
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
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC.P2MKcA.DAssembly"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC.P2MKcA"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC.P2MKcA P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC.P2MKcA.DAssembly"

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
      ∀ H, (f H).ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
          algebraMap K (modularFunctionFieldFullC K N) j₀) =
        (Nat.card {H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
          f H' = f H} : ℤ) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  let F := modularFunctionFieldFullC K N
  let jF : F := ⟨jqModC K, jqModC_mem_full K N⟩
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)

  obtain ⟨M, _iF, _iD, _iA, t, ht, hfin, hgal, W₀, hW₀, θ, ρ, hfull, hθinj, hρE, -, hequivC,
    hsurjC, -⟩ := ModularCurve.exists_equivariant_torsion_reduction_ofJ K p N hN j₀ E₀ hE₀
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

  obtain ⟨Φ, hnatA⟩ := ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_of_transcendental_j
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

  obtain ⟨f, hfS, hfsurj, hfib, hord⟩ := assemble hN0 θ hθ hθs D act hact ρ hρE hequiv hsurj ΦX actX
    hnat π S hπS hπsurj hπfib e hπe
  exact ⟨f, hfS, hfsurj, fun H H' => (hfib H H').trans Iff.rfl, hord⟩

end S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
end P2MW
export P2MW.S_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC (solution)
