-- Prove2me | solution 1 for ModularCurve.two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e8ae9264-0de4-5f90-a7ed-b3775a43be2c

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_PlaceWidthChar
import Theorems.Thm_ModularCurve_moduliPlace_orbitClauses
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_of_isAlgClosed
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Theorems.Thm_WeierstrassCurve_exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq
import Theorems.Thm_WeierstrassCurve_nonempty_stabilizer_variableChange_mulEquiv_units_rationalEndSubring
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_mul_jWidthChar
import Theorems.Thm_WeierstrassCurve_mem_rationalEndSubring_iff_mem_rationalHomSet
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace_of_prime
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

namespace HwCurve

open ModularCurve AlgebraicCurve WeierstrassCurve

theorem nat_div_eq_div_two {J F s : ℕ} (hF : 0 < F) (h : F * s = 2 * J) : J / F = s / 2 := by
  have h2 : (0 : ℕ) < 2 := two_pos
  calc J / F = (2 * J) / (2 * F) := (Nat.mul_div_mul_left J F h2).symm
    _ = (F * s) / (F * 2) := by rw [h, Nat.mul_comm 2 F]
    _ = s / 2 := Nat.mul_div_mul_left s 2 hF

section OrdTransfer

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem ord_eq_ord_map_of_comap_eq (φ : F →+* F') (hφ : Function.Bijective φ)
    (P : Place K F) (v : Place K F')
    (h : P.toValuationSubring = v.toValuationSubring.comap φ) {x : F} (hx : x ≠ 0) :
    P.ord x = v.ord (φ x) := by
  set e : F ≃+* F' := RingEquiv.ofBijective φ hφ with he
  have heφ : ∀ y, e y = φ y := fun y => rfl
  have hmem : ∀ y : F, y ∈ P.toValuationSubring ↔ φ y ∈ v.toValuationSubring := fun y => by
    rw [h, ValuationSubring.mem_comap]

  let eAB : P.toValuationSubring ≃+* v.toValuationSubring :=
    { toFun := fun a => ⟨φ a, (hmem a).mp a.2⟩
      invFun := fun b => ⟨e.symm b, (hmem _).mpr (by rw [← heφ, e.apply_symm_apply]; exact b.2)⟩
      left_inv := fun a => Subtype.ext (by simp only; rw [← heφ, e.symm_apply_apply])
      right_inv := fun b => Subtype.ext (by simp only; rw [← heφ, e.apply_symm_apply])
      map_mul' := fun a b => Subtype.ext (map_mul φ _ _)
      map_add' := fun a b => Subtype.ext (map_add φ _ _) }
  have hcoe_symm : ∀ b : v.toValuationSubring, ((eAB.symm b : P.toValuationSubring) : F) = e.symm b :=
    fun b => rfl
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ₀ : Irreducible (eAB.symm π) := (MulEquiv.irreducible_iff eAB.symm).mpr hπ
  have hφx : φ x ≠ 0 := (map_ne_zero φ).mpr hx
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hφx hπ
  set n := v.ord (φ x) with hn
  let u₀ : P.toValuationSubringˣ := Units.map eAB.symm.toMonoidHom u
  have hx' : x = ((u₀ : P.toValuationSubring) : F) * (((eAB.symm π : P.toValuationSubring) : F) ^ n) := by
    have hx1 : x = e.symm (φ x) := by rw [← heφ, e.symm_apply_apply]
    rw [hx1, hu, map_mul, map_zpow₀]
    rfl
  rw [hx', P.ord_unit_smul_zpow u₀ hπ₀ n]

end OrdTransfer

section Units

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  (W : WeierstrassCurve κ) [W.IsElliptic]

abbrev Pt := (W.baseChange κ).toAffine.Point

abbrev G := (rationalEndSubring κ W)ˣ

abbrev toHom (g : G W) : Pt W →+ Pt W := ((g : rationalEndSubring κ W) : AddMonoid.End (Pt W))

theorem toHom_mul (g h : G W) : toHom W (g * h) = (toHom W g).comp (toHom W h) := rfl

theorem toHom_one : toHom W 1 = AddMonoidHom.id _ := rfl

theorem toHom_inv_comp (g : G W) : (toHom W g⁻¹).comp (toHom W g) = AddMonoidHom.id _ := by
  rw [← toHom_mul, inv_mul_cancel, toHom_one]

theorem toHom_comp_inv (g : G W) : (toHom W g).comp (toHom W g⁻¹) = AddMonoidHom.id _ := by
  rw [← toHom_mul, mul_inv_cancel, toHom_one]

theorem toHom_injective (g : G W) : Function.Injective (toHom W g) := by
  intro a b hab
  have := congrArg (toHom W g⁻¹) hab
  simpa only [← AddMonoidHom.comp_apply, toHom_inv_comp, AddMonoidHom.id_apply] using this

theorem toHom_mem (g : G W) : toHom W g ∈ rationalHomSet κ W W :=
  (mem_rationalEndSubring_iff_mem_rationalHomSet κ W _).mp (g : rationalEndSubring κ W).2

theorem smul_eq_map (g : G W) (H : AddSubgroup (Pt W)) : g • H = H.map (toHom W g) := rfl

def unitOf (ι ι' : Pt W →+ Pt W) (hι : ι ∈ rationalHomSet κ W W) (hι' : ι' ∈ rationalHomSet κ W W)
    (h1 : ι'.comp ι = AddMonoidHom.id _) (h2 : ι.comp ι' = AddMonoidHom.id _) : G W where
  val := ⟨ι, (mem_rationalEndSubring_iff_mem_rationalHomSet κ W _).mpr hι⟩
  inv := ⟨ι', (mem_rationalEndSubring_iff_mem_rationalHomSet κ W _).mpr hι'⟩
  val_inv := Subtype.ext h2
  inv_val := Subtype.ext h1

@[scoped simp] theorem toHom_unitOf (ι ι' : Pt W →+ Pt W) (hι hι' h1 h2) :
    toHom W (unitOf W ι ι' hι hι' h1 h2) = ι := rfl

theorem mem_orbit_iff_exists (H H' : AddSubgroup (Pt W)) :
    H' ∈ MulAction.orbit (G W) H ↔
      ∃ ι ∈ rationalHomSet κ W W, ∃ ι' ∈ rationalHomSet κ W W,
        ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _ ∧ H = H'.map ι := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨toHom W g⁻¹, toHom_mem W _, toHom W g, toHom_mem W _, toHom_comp_inv W g, toHom_inv_comp W g, ?_⟩
    show H = AddSubgroup.map (toHom W g⁻¹) (g • H)
    rw [smul_eq_map, AddSubgroup.map_map, ← toHom_mul, inv_mul_cancel, toHom_one, AddSubgroup.map_id]
  · rintro ⟨ι, hι, ι', hι', h1, h2, hH⟩
    refine MulAction.mem_orbit_iff.mpr ⟨(unitOf W ι ι' hι hι' h1 h2)⁻¹, ?_⟩
    rw [smul_eq_map, hH, AddSubgroup.map_map,
      show (toHom W (unitOf W ι ι' hι hι' h1 h2)⁻¹).comp ι = AddMonoidHom.id _ from
        toHom_inv_comp W (unitOf W ι ι' hι hι' h1 h2), AddSubgroup.map_id]

noncomputable def stabEquiv (C : AddSubgroup (Pt W)) :
    {ι : Pt W →+ Pt W // ι ∈ rationalHomSet κ W W ∧
        (∃ ι' ∈ rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C.map ι = C} ≃ MulAction.stabilizer (G W) C where
  toFun ι := ⟨unitOf W ι.1 ι.2.2.1.choose ι.2.1 ι.2.2.1.choose_spec.1 ι.2.2.1.choose_spec.2.1
      ι.2.2.1.choose_spec.2.2, by
        rw [MulAction.mem_stabilizer_iff, smul_eq_map, toHom_unitOf]; exact ι.2.2.2⟩
  invFun g := ⟨toHom W g, toHom_mem W _, ⟨toHom W g⁻¹, toHom_mem W _, toHom_inv_comp W _, toHom_comp_inv W _⟩, by
      rw [← smul_eq_map]; exact g.2⟩
  left_inv ι := Subtype.ext rfl
  right_inv g := Subtype.ext (Units.ext (Subtype.ext rfl))

theorem isAddCyclic_and_card_smul (g : G W) (H : AddSubgroup (Pt W)) {n : ℕ}
    (hH : IsAddCyclic H ∧ Nat.card H = n) : IsAddCyclic ↥(g • H) ∧ Nat.card ↥(g • H) = n := by
  rw [smul_eq_map]
  have e : H ≃+ H.map (toHom W g) := H.equivMapOfInjective _ (toHom_injective W g)
  haveI := hH.1
  exact ⟨isAddCyclic_of_surjective e e.surjective, by rw [← hH.2]; exact Nat.card_congr e.symm.toEquiv⟩

theorem natCard_G (p : ℕ) [Fact p.Prime] [CharP κ p] : Nat.card (G W) = 2 * jWidthChar p W.j := by
  obtain ⟨e⟩ := nonempty_stabilizer_variableChange_mulEquiv_units_rationalEndSubring (F := κ) κ W
  rw [← Nat.card_congr e.toEquiv]
  exact natCard_stabilizer_variableChange_eq_two_mul_jWidthChar κ p W

theorem card_orbit_mul_card_stabilizer (C : AddSubgroup (Pt W)) :
    Nat.card (MulAction.orbit (G W) C) * Nat.card (MulAction.stabilizer (G W) C) = Nat.card (G W) := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, Subgroup.index_mul_card]

theorem toHom_neg_one_apply (x : Pt W) : toHom W (-1) x = -x := rfl

theorem neg_one_smul_eq (H : AddSubgroup (Pt W)) : (-1 : G W) • H = H := by
  rw [smul_eq_map]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [toHom_neg_one_apply]
    exact H.neg_mem hy
  · intro hx
    exact ⟨-x, H.neg_mem hx, by rw [toHom_neg_one_apply, neg_neg]⟩

theorem neg_one_ne_one (n : ℕ) (hn3 : 3 ≤ n) (hnκ : (n : κ) ≠ 0) : (-1 : G W) ≠ 1 := by
  intro h
  obtain ⟨T, hT⟩ := exists_addOrderOf_eq_of_isAlgClosed W n (by exact_mod_cast hnκ)
  have hneg : -T = T := by
    have := congrArg (fun g : G W => toHom W g T) h
    simp only [toHom_neg_one_apply, toHom_one, AddMonoidHom.id_apply] at this
    exact this
  have h2 : 2 • T = 0 := by
    rw [two_nsmul]
    nth_rewrite 1 [← hneg]
    exact neg_add_cancel T
  have hdvd : addOrderOf T ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero h2
  rw [hT] at hdvd
  exact absurd (Nat.le_of_dvd two_pos hdvd) (by omega)

theorem two_dvd_card_stabilizer (n : ℕ) (hn3 : 3 ≤ n) (hnκ : (n : κ) ≠ 0) (C : AddSubgroup (Pt W)) :
    2 ∣ Nat.card (MulAction.stabilizer (G W) C) := by
  have hmem : (-1 : G W) ∈ MulAction.stabilizer (G W) C := neg_one_smul_eq W C
  have hord : orderOf (⟨-1, hmem⟩ : MulAction.stabilizer (G W) C) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [neg_one_sq]) (neg_one_ne_one W n hn3 hnκ)
  rw [← hord]
  exact orderOf_dvd_natCard _

noncomputable def fibEquivOrbit {M' : ℕ} (C : AddSubgroup (Pt W)) (hC : IsAddCyclic C ∧ Nat.card C = M')
    (p : {C' : AddSubgroup (Pt W) // IsAddCyclic C' ∧ Nat.card C' = M'} → Prop)
    (hp : ∀ C', p C' ↔ C'.1 ∈ MulAction.orbit (G W) C) :
    {C' // p C'} ≃ MulAction.orbit (G W) C where
  toFun C' := ⟨C'.1.1, (hp C'.1).mp C'.2⟩
  invFun H := ⟨⟨H.1, by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp H.2
      rw [← hg]
      exact isAddCyclic_and_card_smul W g C hC⟩, (hp _).mpr H.2⟩
  left_inv C' := rfl
  right_inv H := rfl

end Units

section Moduli

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem inclusion_bijective_of_eq {E E' : IntermediateField κ (LaurentSeries κ)} (hle : E ≤ E') (heq : E = E') :
    Function.Bijective (IntermediateField.inclusion hle) := by
  subst heq
  exact ⟨IntermediateField.inclusion_injective hle, fun y => ⟨y, rfl⟩⟩

end Moduli

section Interface

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem La_ord_moduliPlace_sub_pos_and_eq_natCard
    (M' : ℕ) [NeZero M'] (hM' : ((M' : ℕ) : κ) ≠ 0)
    (W : WeierstrassCurve κ) [W.IsElliptic] (C : AddSubgroup W.toAffine.Point)
    (hcyc : IsAddCyclic C) (hcard : Nat.card C = M') :
    0 < (moduliPlace κ M' W C).ord
        ((⟨jqModC κ, jqModC_mem_full κ M'⟩ : ↥(modularFunctionFieldFullC κ M')) -
          algebraMap κ ↥(modularFunctionFieldFullC κ M') W.j) ∧
    (moduliPlace κ M' W C).ord
        ((⟨jqModC κ, jqModC_mem_full κ M'⟩ : ↥(modularFunctionFieldFullC κ M')) -
          algebraMap κ ↥(modularFunctionFieldFullC κ M') W.j) =
      (Nat.card {C' : {C' : AddSubgroup W.toAffine.Point // IsAddCyclic C' ∧ Nat.card C' = M'} //
        moduliPlace κ M' W C'.1 = moduliPlace κ M' W C} : ℤ) := by
  obtain ⟨h1, -, -, h4⟩ := moduliPlace_orbitClauses κ M' hM' (eq_of_isModuliPlaceOf κ M' hM')
  exact ⟨h1 W ⟨C, hcyc, hcard⟩, h4 W ⟨C, hcyc, hcard⟩⟩

theorem Lb_placeRamificationJ_eq_natCard_and_evalAt_jGeomGen_eq
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (M' : ℕ) [NeZero M'] (hq'M' : ¬ q' ∣ M')
    (W : WeierstrassCurve κ) [W.IsElliptic] (C : AddSubgroup W.toAffine.Point)
    (hcyc : IsAddCyclic C) (hcard : Nat.card C = M')
    (P : Place κ ↥(modularFunctionFieldC κ M'))
    (hP : P.toValuationSubring =
      (moduliPlace κ M' W C).toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full κ M')).toRingHom) :
    placeRamificationJ M' P =
      Nat.card {C' : {C' : AddSubgroup W.toAffine.Point // IsAddCyclic C' ∧ Nat.card C' = M'} //
        moduliPlace κ M' W C'.1 = moduliPlace κ M' W C} ∧
    P.evalAt (jGeomGen κ M') = W.j := by
  have hM' : ((M' : ℕ) : κ) ≠ 0 := fun h => hq'M' ((CharP.cast_eq_zero_iff κ q' M').mp h)
  obtain ⟨hpos, hcount⟩ := La_ord_moduliPlace_sub_pos_and_eq_natCard M' hM' W C hcyc hcard

  set φ := (IntermediateField.inclusion (modularFunctionFieldC_le_full κ M')).toRingHom with hφdef
  have hφ : Function.Bijective φ :=
    inclusion_bijective_of_eq (modularFunctionFieldC_le_full κ M')
      (modularFunctionFieldC_eq_modularFunctionFieldFullC κ q' M' hq'M')
  have hφj : φ (jGeomGen κ M' - algebraMap κ ↥(modularFunctionFieldC κ M') W.j) =
      (⟨jqModC κ, jqModC_mem_full κ M'⟩ : ↥(modularFunctionFieldFullC κ M')) -
        algebraMap κ ↥(modularFunctionFieldFullC κ M') W.j := by
    rw [map_sub]
    congr 1
  have hne : jGeomGen κ M' - algebraMap κ ↥(modularFunctionFieldC κ M') W.j ≠ 0 :=
    jGeomGen_sub_algebraMap_ne_zero κ M' W.j
  have hordP : P.ord (jGeomGen κ M' - algebraMap κ ↥(modularFunctionFieldC κ M') W.j) =
      (Nat.card {C' : {C' : AddSubgroup W.toAffine.Point // IsAddCyclic C' ∧ Nat.card C' = M'} //
        moduliPlace κ M' W C'.1 = moduliPlace κ M' W C} : ℤ) := by
    rw [ord_eq_ord_map_of_comap_eq φ hφ P _ hP hne, hφj, hcount]
  have hposP : 0 < P.ord (jGeomGen κ M' - algebraMap κ ↥(modularFunctionFieldC κ M') W.j) := by
    rw [ord_eq_ord_map_of_comap_eq φ hφ P _ hP hne, hφj]; exact hpos

  have hmem : jGeomGen κ M' ∈ P.toValuationSubring := by
    have := add_mem (P.mem_of_ord_nonneg hne hposP.le) (P.algebraMap_mem' W.j)
    rwa [sub_add_cancel] at this
  have hev : P.evalAt (jGeomGen κ M') = W.j := by
    rw [P.evalAt_congr hmem (P.algebraMap_mem' W.j) (Or.inr hposP), P.evalAt_algebraMap]
  refine ⟨?_, hev⟩
  show (P.ord (jGeomGen κ M' - algebraMap κ ↥(modularFunctionFieldC κ M') (P.evalAt (jGeomGen κ M')))).toNat = _
  rw [hev, hordP, Int.toNat_natCast]

theorem Le_two_mul_div_eq {J F s : ℕ} (hF : 0 < F) (h : F * s = 2 * J) (hs : 2 ∣ s) :
    2 * (J / F) = s ∧ J / F = s / 2 :=
  ⟨(congrArg (2 * ·) (nat_div_eq_div_two hF h)).trans (Nat.mul_div_cancel' hs), nat_div_eq_div_two hF h⟩

end Interface

end HwCurve
p2m_reactivate "P2MW.S_ModularCurve_two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace_of_prime.HwCurve"

open HwCurve in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (M' : ℕ) [NeZero M'] (hq'M' : ¬ q' ∣ M')
    (W : WeierstrassCurve κ) [W.IsElliptic] (C : AddSubgroup W.toAffine.Point)
    (hcyc : IsAddCyclic C) (hcard : Nat.card C = M')
    (P : Place κ ↥(modularFunctionFieldC κ M'))
    (hP : P.toValuationSubring =
      (moduliPlace κ M' W C).toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full κ M')).toRingHom) :
    2 * placeWidthChar q' M' P =
      Nat.card {ι : W.toAffine.Point →+ W.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ W W ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C.map ι = C} := by

  obtain ⟨n, hn3, hnκ⟩ : ∃ n : ℕ, 3 ≤ n ∧ (n : κ) ≠ 0 := by
    by_cases h3 : q' = 3
    · refine ⟨4, by norm_num, fun h => ?_⟩
      have hdvd : q' ∣ 4 := (CharP.cast_eq_zero_iff κ q' 4).mp (by exact_mod_cast h)
      rw [h3] at hdvd
      exact absurd hdvd (by decide)
    · refine ⟨3, le_rfl, fun h => ?_⟩
      have hdvd : q' ∣ 3 := (CharP.cast_eq_zero_iff κ q' 3).mp (by exact_mod_cast h)
      exact h3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : q'.Prime) Nat.prime_three).mp hdvd)
  have hN : ((M' : ℕ) : κ) ≠ 0 := fun h => hq'M' ((CharP.cast_eq_zero_iff κ q' M').mp h)

  obtain ⟨hram, hev⟩ :=
    Lb_placeRamificationJ_eq_natCard_and_evalAt_jGeomGen_eq q' M' hq'M' W C hcyc hcard P hP

  obtain ⟨-, -, h3cl, -⟩ := moduliPlace_orbitClauses κ M' hN (eq_of_isModuliPlaceOf κ M' hN)
  have hfib : ∀ C' : {C' : AddSubgroup (Pt W) // IsAddCyclic C' ∧ Nat.card C' = M'},
      moduliPlace κ M' W C'.1 = moduliPlace κ M' W C ↔ C'.1 ∈ @MulAction.orbit (G W) (AddSubgroup (Pt W)) _ C := by
    intro C'
    refine (h3cl W W C' ⟨C, hcyc, hcard⟩).trans ?_
    refine (WeierstrassCurve.exists_rationalHomSet_comp_eq_id_map_eq_iff_exists_variableChange_smul_eq
      M' W W C'.1 C'.2.2 C hcard).symm.trans ?_
    exact (mem_orbit_iff_exists W C C'.1).symm
  have eF := fibEquivOrbit W (C : AddSubgroup (Pt W)) ⟨hcyc, hcard⟩ _ hfib
  have eS := stabEquiv W (C : AddSubgroup (Pt W))

  have hG := natCard_G W q'
  have hos := card_orbit_mul_card_stabilizer W (C : AddSubgroup (Pt W))
  rw [← Nat.card_congr eF, ← Nat.card_congr eS, hG] at hos
  have hF : 0 < Nat.card {C' : {C' : AddSubgroup (Pt W) // IsAddCyclic C' ∧ Nat.card C' = M'} //
      moduliPlace κ M' W C'.1 = moduliPlace κ M' W C} := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hos
    have := jWidthChar_pos q' W.j
    omega

  have h2S := two_dvd_card_stabilizer W n hn3 hnκ C
  rw [← Nat.card_congr eS] at h2S
  show 2 * (jWidthChar q' (P.evalAt (jGeomGen κ M')) / placeRamificationJ M' P) = _
  rw [hev, hram]
  exact (congrArg (2 * ·) (nat_div_eq_div_two hF hos)).trans (Nat.mul_div_cancel' h2S)

end S_ModularCurve_two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace_of_prime
end P2MW
export P2MW.S_ModularCurve_two_mul_placeWidthChar_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace_of_prime (solution)
