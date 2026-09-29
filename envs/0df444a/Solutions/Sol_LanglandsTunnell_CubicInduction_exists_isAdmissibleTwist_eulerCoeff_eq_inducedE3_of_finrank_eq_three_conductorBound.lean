-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/25cbae55-617b-5ba9-8bc2-484407cfaecc

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Theorems.Thm_LanglandsTunnell_CubicLambda_exists_resolventChar
import Theorems.Thm_LanglandsTunnell_CubicLambda_zetaEulerPoly_eq_of_resolvent
import Theorems.Thm_LanglandsTunnell_CubicLambda_zetaEulerPoly_eq_of_resolvent_of_ramified
import Theorems.Thm_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_of_isGalois_of_prime_finrank
import Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq
import Theorems.Thm_LanglandsTunnell_CubicLambda_exists_int_jacobiSym_eq_of_finrank_eq_two
import Theorems.Thm_LanglandsTunnell_CubicLambda_dirichletChar_neg_one_eq_of_forall_eq_jacobiSym
import Theorems.Thm_NumberField_TateGlobal_exists_hasConductorExponentAt_localChar_comp_genuineBeta_le
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_le_three_of_pow_two_eq_one
import Mathlib.Data.Finite.Perm
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Rat.Cast.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.classAct_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"
set_option Elab.async false

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField NumberField.TateGlobal LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.LanglandsTunnell.CubicLambda"

section

p2m_open "IsDedekindDomain NumberField P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField NumberField.InfinitePlace HeckeCharacter LanglandsTunnell.Converse"
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.LanglandsTunnell.CubicLambda"

section

p2m_open "IsDedekindDomain NumberField P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField NumberField.InfinitePlace.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.TateGlobal LanglandsTunnell.Converse"
open NumberField.InfinitePlace.Completion

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.higherUnitsAt TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt RankinSelberg.primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly TateLocal.exists_hasConductorExponentAt_le_three_of_pow_two_eq_one"
namespace CubicLambda
p2m_export "LanglandsTunnell.CubicLambda" "eulerCoeff zetaEulerPoly resolventSignBit exists_resolventChar zetaEulerPoly_eq_of_resolvent zetaEulerPoly_eq_of_resolvent_of_ramified exists_isFiniteOrderHeckeChar_eulerCoeff_of_isGalois_of_prime_finrank exists_int_jacobiSym_eq_of_finrank_eq_two dirichletChar_neg_one_eq_of_forall_eq_jacobiSym"
namespace DirichletArch
p2m_open "LanglandsTunnell.CubicLambda LanglandsTunnell"

private theorem infinitePlace_eq_rat (w : InfinitePlace ℚ) : w = Rat.infinitePlace := Subsingleton.elim _ _

private theorem archCentralUnit_snd_apply (x : (Rat.infinitePlace.Completion)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((NumberField.AdelicVolume.archCentralUnit ℚ Rat.infinitePlace x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
      AdeleRing (𝓞 ℚ) ℚ).2 v = 1 := by
  rw [NumberField.AdelicVolume.archCentralUnit_snd]
  rfl

private theorem archCoord_archCentralUnit (x : (Rat.infinitePlace.Completion)ˣ) :
    RatIdele.archCoord (NumberField.AdelicVolume.archCentralUnit ℚ Rat.infinitePlace x)
      = ringEquivRealOfIsReal Rat.isReal_infinitePlace (x : Rat.infinitePlace.Completion) := by
  unfold RatIdele.archCoord
  rw [NumberField.AdelicVolume.archCentralUnit_fst_self]

private theorem extensionEmbedding_eq_ofReal (y : Rat.infinitePlace.Completion) :
    extensionEmbedding Rat.infinitePlace y
      = ((ringEquivRealOfIsReal Rat.isReal_infinitePlace y : ℝ) : ℂ) :=
  (extensionEmbeddingOfIsReal_apply Rat.isReal_infinitePlace y).symm

private theorem norm_eq_abs_real (y : Rat.infinitePlace.Completion) :
    ‖y‖ = |ringEquivRealOfIsReal Rat.isReal_infinitePlace y| := by
  rw [ringEquivRealOfIsReal_apply, ← Real.norm_eq_abs]
  exact ((isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) y).symm

private theorem coord_neg_one :
    ringEquivRealOfIsReal Rat.isReal_infinitePlace
      (((-1 : (Rat.infinitePlace.Completion)ˣ)) : Rat.infinitePlace.Completion) < 0 := by
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
  norm_num

private theorem div_norm_of_neg (y : Rat.infinitePlace.Completion)
    (hy : ringEquivRealOfIsReal Rat.isReal_infinitePlace y < 0) :
    extensionEmbedding Rat.infinitePlace y / ((‖y‖ : ℝ) : ℂ) = -1 := by
  rw [extensionEmbedding_eq_ofReal, norm_eq_abs_real, abs_of_neg hy]
  push_cast
  rw [div_neg, div_self (Complex.ofReal_ne_zero.mpr hy.ne)]

private theorem div_norm_of_pos (y : Rat.infinitePlace.Completion)
    (hy : 0 < ringEquivRealOfIsReal Rat.isReal_infinitePlace y) :
    extensionEmbedding Rat.infinitePlace y / ((‖y‖ : ℝ) : ℂ) = 1 := by
  rw [extensionEmbedding_eq_ofReal, norm_eq_abs_real, abs_of_pos hy,
    div_self (Complex.ofReal_ne_zero.mpr hy.ne')]

private
theorem coe_archLocalChar_dirichletIdeleChar_of_neg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x : (Rat.infinitePlace.Completion)ˣ)
    (hx : ringEquivRealOfIsReal Rat.isReal_infinitePlace (x : Rat.infinitePlace.Completion) < 0) :
    ((archLocalChar χ.dirichletIdeleChar Rat.infinitePlace x : ℂˣ) : ℂ) = χ (-1) := by
  rw [archLocalChar_apply]
  exact DirichletCharacter.coe_dirichletIdeleChar_of_snd_eq_one_of_neg χ (archCentralUnit_snd_apply x)
    (by rw [archCoord_archCentralUnit]; exact hx)

private
theorem coe_archLocalChar_dirichletIdeleChar_of_pos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x : (Rat.infinitePlace.Completion)ˣ)
    (hx : 0 < ringEquivRealOfIsReal Rat.isReal_infinitePlace (x : Rat.infinitePlace.Completion)) :
    ((archLocalChar χ.dirichletIdeleChar Rat.infinitePlace x : ℂˣ) : ℂ) = 1 := by
  rw [archLocalChar_apply, DirichletCharacter.dirichletIdeleChar_eq_one_of_snd_eq_one_of_pos χ
    (archCentralUnit_snd_apply x) (by rw [archCoord_archCentralUnit]; exact hx), Units.val_one]

private
theorem isArchCompAt_dirichletIdeleChar_zero_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (w : InfinitePlace ℚ) (a : ℤ) :
    IsArchCompAt ℚ χ.dirichletIdeleChar w 0 a ↔ χ (-1) = (-1 : ℂ) ^ a := by
  have hw := infinitePlace_eq_rat w
  subst hw
  constructor
  · intro h
    have hx := h (-1)
    rw [mul_zero, Complex.cpow_zero, one_mul, coe_archLocalChar_dirichletIdeleChar_of_neg χ (-1) coord_neg_one,
      div_norm_of_neg _ coord_neg_one] at hx
    exact hx
  · intro h x
    rw [mul_zero, Complex.cpow_zero, one_mul]
    have hx0 : ringEquivRealOfIsReal Rat.isReal_infinitePlace (x : Rat.infinitePlace.Completion) ≠ 0 :=
      (map_ne_zero _).mpr x.ne_zero
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · rw [coe_archLocalChar_dirichletIdeleChar_of_neg χ x hneg, div_norm_of_neg _ hneg]
      exact h
    · rw [coe_archLocalChar_dirichletIdeleChar_of_pos χ x hpos, div_norm_of_pos _ hpos, one_zpow]

private
theorem isArchCompAt_dirichletIdeleChar_resolventSignBit (L : Type) [Field L] [NumberField L]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : χ (-1) = if nrComplexPlaces L = 0 then 1 else -1) (w : InfinitePlace ℚ) :
    IsArchCompAt ℚ χ.dirichletIdeleChar w 0 ((resolventSignBit L).val : ℤ) := by
  rw [isArchCompAt_dirichletIdeleChar_zero_iff, h]
  unfold resolventSignBit
  split_ifs
  · rw [show (((0 : ZMod 2).val : ℕ) : ℤ) = 0 by decide, zpow_zero]
  · rw [show (((1 : ZMod 2).val : ℕ) : ℤ) = 1 by decide, zpow_one]

private
theorem isArchCompAt_dirichletIdeleChar_of_neg_one_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : χ (-1) = 1) (w : InfinitePlace ℚ) :
    IsArchCompAt ℚ χ.dirichletIdeleChar w 0 (((0 : ZMod 2)).val : ℤ) := by
  rw [isArchCompAt_dirichletIdeleChar_zero_iff, h, show (((0 : ZMod 2).val : ℕ) : ℤ) = 0 by decide, zpow_zero]

private
theorem neg_one_eq_one_of_dirichletIdeleChar_pow_three_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : χ.dirichletIdeleChar ^ 3 = 1) : χ (-1) = 1 := by
  have h3 : χ (-1) ^ 3 = 1 := by
    have hx : ((archLocalChar (χ.dirichletIdeleChar ^ 3) Rat.infinitePlace (-1) : ℂˣ) : ℂ) = 1 := by
      rw [h]
      rfl
    have hpow : ((archLocalChar (χ.dirichletIdeleChar ^ 3) Rat.infinitePlace (-1) : ℂˣ) : ℂ)
        = ((archLocalChar χ.dirichletIdeleChar Rat.infinitePlace (-1) : ℂˣ) : ℂ) ^ 3 := by
      rw [archLocalChar_apply, archLocalChar_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rw [hpow, coe_archLocalChar_dirichletIdeleChar_of_neg χ (-1) coord_neg_one] at hx
    exact hx
  have h2 : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have h32 : χ (-1) ^ 3 = (χ (-1) * χ (-1)) * χ (-1) := by ring
  rw [h2, one_mul] at h32
  exact h32.symm.trans h3

private
theorem isArchCompAt_dirichletIdeleChar_of_pow_three_eq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : χ.dirichletIdeleChar ^ 3 = 1) (w : InfinitePlace ℚ) :
    IsArchCompAt ℚ χ.dirichletIdeleChar w 0 (((0 : ZMod 2)).val : ℤ) :=
  isArchCompAt_dirichletIdeleChar_of_neg_one_eq_one χ (neg_one_eq_one_of_dirichletIdeleChar_pow_three_eq_one χ h) w

end LanglandsTunnell.CubicLambda.DirichletArch

end

section

open Module Polynomial IntermediateField

p2m_open_scoped "NumberField P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField NumberField.InfinitePlace.NumberField IntermediateField"

namespace NumberField
p2m_export "NumberField" "ComplexEmbedding.isReal_iff InfinitePlace.nrRealPlaces IsTotallyReal.of_algebra IsTotallyReal.isReal InfinitePlace.not_isComplex_iff_isReal place maximalRealSubfield_eq_top_iff_isTotallyReal InfinitePlace.Completion mem_maximalRealSubfield_iff to_finiteDimensional RingOfIntegers InfinitePlace.not_isReal_iff_isComplex RingOfIntegers.ker_algebraMap_eq_bot IsTotallyReal.complexEmbedding_isReal InfinitePlace.nrComplexPlaces maximalRealSubfield InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal InfinitePlace IsTotallyReal AdeleRing InfinitePlace.card_add_two_mul_card_eq_rank to_charZero InfinitePlace.isUnramified inst_ringOfIntegersAlgebra InfinitePlace.LiesOver.isometry_algebraMap IsTotallyReal.nrComplexPlaces_eq_zero nrComplexPlaces_eq_zero_iff InfinitePlace.isUnramified_iff ComplexEmbedding.conjugate_coe_eq AdelicLevel.finAdeleEval AdelicLevel.adeleArch AdelicLevel.adeleFin AdelicLevel.finIncl AdelicLevel.finIncl_apply_fst AdelicLevel.finIncl_apply_snd AdelicLevel.localUnit AdelicLevel.localUnit_apply_self AdelicLevel.localUnit_apply_of_ne AdelicLevel.uniformizerUnit AdelicLevel.valued_uniformizerUnit TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicVolume.archCentralUnit AdelicVolume.archCentralUnit_snd AdelicVolume.archCentralUnit_fst_self TateGlobal.exists_hasConductorExponentAt_localChar_comp_genuineBeta_le"
p2m_open "NumberField"

namespace WildResolventCarrier

variable (K : Type*) [Field K] [NumberField K]

private
noncomputable def primElt : K :=
  (Field.exists_primitive_element ℚ K).choose

private
theorem adjoin_primElt_eq_top : ℚ⟮primElt K⟯ = ⊤ :=
  (Field.exists_primitive_element ℚ K).choose_spec

private
theorem isIntegral_primElt : IsIntegral ℚ (primElt K) :=
  IsIntegral.of_finite ℚ _

private
theorem natDegree_minpoly_primElt (hK3 : finrank ℚ K = 3) :
    (minpoly ℚ (primElt K)).natDegree = 3 := by
  rw [← IntermediateField.adjoin.finrank (isIntegral_primElt K), adjoin_primElt_eq_top,
    IntermediateField.finrank_top']
  exact hK3

private
noncomputable abbrev GalClosure : Type _ :=
  (minpoly ℚ (primElt K)).SplittingField

private
scoped instance : NumberField (GalClosure K) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

private
scoped instance : IsGalois ℚ (GalClosure K) :=
  haveI : IsSplittingField ℚ (GalClosure K) (minpoly ℚ (primElt K)) :=
    Polynomial.IsSplittingField.splittingField _
  IsGalois.of_separable_splitting_field
    ((minpoly.irreducible (isIntegral_primElt K)).separable)

private
theorem card_aroots_pos :
    0 < ((minpoly ℚ (primElt K)).aroots (GalClosure K)).card := by
  rw [Multiset.card_pos]
  exact (Polynomial.SplittingField.splits (minpoly ℚ (primElt K))).roots_ne_zero
    (by rw [Polynomial.natDegree_map]
        exact (minpoly.natDegree_pos (isIntegral_primElt K)).ne')

private
noncomputable def aRoot : GalClosure K :=
  (Multiset.card_pos_iff_exists_mem.mp (card_aroots_pos K)).choose

private
theorem aRoot_mem : aRoot K ∈ (minpoly ℚ (primElt K)).aroots (GalClosure K) :=
  (Multiset.card_pos_iff_exists_mem.mp (card_aroots_pos K)).choose_spec

private
noncomputable def toGalClosure : K →ₐ[ℚ] GalClosure K :=
  ((IntermediateField.algHomAdjoinIntegralEquiv ℚ (isIntegral_primElt K)).symm
      ⟨aRoot K, aRoot_mem K⟩).comp
    (((IntermediateField.equivOfEq (adjoin_primElt_eq_top K)).trans
      IntermediateField.topEquiv).symm.toAlgHom)

private
theorem toGalClosure_injective : Function.Injective (toGalClosure K) :=
  (toGalClosure K).toRingHom.injective

private
noncomputable scoped instance instAlgebraGalClosure : Algebra K (GalClosure K) :=
  (toGalClosure K).toRingHom.toAlgebra

private
scoped instance : IsScalarTower ℚ K (GalClosure K) :=
  IsScalarTower.of_algebraMap_eq fun x => ((toGalClosure K).commutes x).symm

private
scoped instance : FiniteDimensional K (GalClosure K) :=
  Module.Finite.right ℚ K (GalClosure K)

private
scoped instance : IsGalois K (GalClosure K) :=
  IsGalois.tower_top_of_isGalois ℚ K (GalClosure K)

private
theorem finrank_galClosure_dvd_six (hK3 : finrank ℚ K = 3) :
    finrank ℚ (GalClosure K) ∣ 6 := by
  classical
  haveI : Fact (((minpoly ℚ (primElt K)).map
      (algebraMap ℚ (GalClosure K))).Splits) :=
    ⟨Polynomial.SplittingField.splits _⟩
  have hsep : (minpoly ℚ (primElt K)).Separable :=
    (minpoly.irreducible (isIntegral_primElt K)).separable

  have hcard : Nat.card (minpoly ℚ (primElt K)).Gal = finrank ℚ (GalClosure K) :=
    Polynomial.Gal.card_of_separable hsep

  have hdvd : Nat.card (minpoly ℚ (primElt K)).Gal ∣
      Nat.card (Equiv.Perm
        ((minpoly ℚ (primElt K)).rootSet (GalClosure K))) :=
    Subgroup.card_dvd_of_injective _
      (Polynomial.Gal.galActionHom_injective (minpoly ℚ (primElt K)) (GalClosure K))
  rw [hcard] at hdvd
  refine hdvd.trans (dvd_of_eq ?_)

  have hsplit : ((minpoly ℚ (primElt K)).map (algebraMap ℚ (GalClosure K))).Splits :=
    Polynomial.SplittingField.splits _
  rw [Nat.card_perm, Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree hsep hsplit, natDegree_minpoly_primElt K hK3]
  rfl

private
theorem finrank_galClosure_eq_three_mul (hK3 : finrank ℚ K = 3) :
    finrank ℚ (GalClosure K) = 3 * finrank K (GalClosure K) := by
  rw [← hK3]
  exact (Module.finrank_mul_finrank ℚ K (GalClosure K)).symm

private
theorem finrank_galClosure_top_dvd_two (hK3 : finrank ℚ K = 3) :
    finrank K (GalClosure K) ∣ 2 := by
  obtain ⟨c, hc⟩ := (finrank_galClosure_eq_three_mul K hK3) ▸ finrank_galClosure_dvd_six K hK3
  refine ⟨c, ?_⟩
  have h3 : 3 * (finrank K (GalClosure K) * c) = 3 * 2 := by rw [← mul_assoc, ← hc]
  omega

private
theorem normal_of_finrank_galClosure_top_eq_one (h1 : finrank K (GalClosure K) = 1) :
    Normal ℚ K := by

  have hsurj : Function.Surjective (toGalClosure K) := by
    intro x
    have hx : x ∈ (⊥ : Subalgebra K (GalClosure K)) := by
      rw [Subalgebra.bot_eq_top_of_finrank_eq_one h1]
      trivial
    exact Algebra.mem_bot.mp hx

  exact Normal.of_algEquiv
    (AlgEquiv.ofBijective (toGalClosure K) ⟨toGalClosure_injective K, hsurj⟩).symm

private
scoped instance (H : Subgroup (GalClosure K ≃ₐ[ℚ] GalClosure K)) :
    NumberField (IntermediateField.fixedField H) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

private
theorem card_aut_galClosure :
    Nat.card (GalClosure K ≃ₐ[ℚ] GalClosure K) = finrank ℚ (GalClosure K) :=
  IsGalois.card_aut_eq_finrank ℚ (GalClosure K)

private
theorem exists_finrank_fixedField_eq_two (h6 : finrank ℚ (GalClosure K) = 6) :
    ∃ H : Subgroup (GalClosure K ≃ₐ[ℚ] GalClosure K),
      finrank ℚ (IntermediateField.fixedField H) = 2 ∧
      finrank (IntermediateField.fixedField H) (GalClosure K) = 3 := by
  classical

  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := GalClosure K ≃ₐ[ℚ] GalClosure K) 3
    (by rw [card_aut_galClosure K, h6]; norm_num)

  have h3 : finrank (IntermediateField.fixedField (Subgroup.zpowers g)) (GalClosure K)
      = 3 := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hg]

  refine ⟨Subgroup.zpowers g, ?_, h3⟩
  have htower := Module.finrank_mul_finrank ℚ
    (IntermediateField.fixedField (Subgroup.zpowers g)) (GalClosure K)
  rw [h3, h6] at htower
  omega

private
theorem finrank_galClosure_eq_six_of_not_normal (hK3 : finrank ℚ K = 3) (hKn : ¬ Normal ℚ K) :
    finrank ℚ (GalClosure K) = 6 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (finrank_galClosure_top_dvd_two K hK3) with h1 | h2
  · exact absurd (normal_of_finrank_galClosure_top_eq_one K h1) hKn
  · rw [finrank_galClosure_eq_three_mul K hK3, h2]

open scoped Classical in

private
noncomputable def resolventSubgroup : Subgroup (GalClosure K ≃ₐ[ℚ] GalClosure K) :=
  if h : ∃ H : Subgroup (GalClosure K ≃ₐ[ℚ] GalClosure K),
      finrank ℚ (IntermediateField.fixedField H) = 2 ∧
      finrank (IntermediateField.fixedField H) (GalClosure K) = 3
    then h.choose else ⊤

private
noncomputable abbrev resolventField : Type :=
  ↥(IntermediateField.fixedField (resolventSubgroup K))

private
theorem finrank_resolventField (hK3 : finrank ℚ K = 3) (hKn : ¬ Normal ℚ K) :
    finrank ℚ (resolventField K) = 2 := by
  have h := exists_finrank_fixedField_eq_two K (finrank_galClosure_eq_six_of_not_normal K hK3 hKn)
  unfold resolventField resolventSubgroup
  rw [dif_pos h]
  exact h.choose_spec.1

private
theorem ringHom_ringOfIntegers_rat_ext {S : Type*} [Ring S] (f g : 𝓞 ℚ →+* S) : f = g := by
  have h : f.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = g.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  ext x
  have hx : x = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) :=
    (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm
  rw [hx]
  exact RingHom.congr_fun h _

private
scoped instance instIsScalarTower_galClosure [Algebra (𝓞 ℚ) (𝓞 K)] :
    IsScalarTower (𝓞 ℚ) (𝓞 K) (𝓞 (GalClosure K)) :=
  IsScalarTower.of_algebraMap_eq' (ringHom_ringOfIntegers_rat_ext _ _)

private
scoped instance instIsScalarTower_resolventField [Algebra (𝓞 ℚ) (𝓞 (resolventField K))] :
    IsScalarTower (𝓞 ℚ) (𝓞 (resolventField K)) (𝓞 (GalClosure K)) :=
  IsScalarTower.of_algebraMap_eq' (ringHom_ringOfIntegers_rat_ext _ _)
end WildResolventCarrier
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier"

end NumberField
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

namespace NumberField
p2m_export "NumberField" "ComplexEmbedding.isReal_iff InfinitePlace.nrRealPlaces IsTotallyReal.of_algebra IsTotallyReal.isReal InfinitePlace.not_isComplex_iff_isReal place maximalRealSubfield_eq_top_iff_isTotallyReal InfinitePlace.Completion mem_maximalRealSubfield_iff to_finiteDimensional RingOfIntegers InfinitePlace.not_isReal_iff_isComplex RingOfIntegers.ker_algebraMap_eq_bot IsTotallyReal.complexEmbedding_isReal InfinitePlace.nrComplexPlaces maximalRealSubfield InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal InfinitePlace IsTotallyReal AdeleRing InfinitePlace.card_add_two_mul_card_eq_rank to_charZero InfinitePlace.isUnramified inst_ringOfIntegersAlgebra InfinitePlace.LiesOver.isometry_algebraMap IsTotallyReal.nrComplexPlaces_eq_zero nrComplexPlaces_eq_zero_iff InfinitePlace.isUnramified_iff ComplexEmbedding.conjugate_coe_eq AdelicLevel.finAdeleEval AdelicLevel.adeleArch AdelicLevel.adeleFin AdelicLevel.finIncl AdelicLevel.finIncl_apply_fst AdelicLevel.finIncl_apply_snd AdelicLevel.localUnit AdelicLevel.localUnit_apply_self AdelicLevel.localUnit_apply_of_ne AdelicLevel.uniformizerUnit AdelicLevel.valued_uniformizerUnit TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicVolume.archCentralUnit AdelicVolume.archCentralUnit_snd AdelicVolume.archCentralUnit_fst_self TateGlobal.exists_hasConductorExponentAt_localChar_comp_genuineBeta_le"
namespace ResolventSignature
p2m_open "NumberField"

private
theorem _root_.NumberField.ResolventSignature.isScalarTower_rat (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] : IsScalarTower ℚ K E :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

p2m_export "NumberField.ResolventSignature" "isScalarTower_rat"

private
theorem isComplex_comap_of_odd_finrank (L E : Type) [Field L] [NumberField L] [Field E]
    [NumberField E] [Algebra L E] [IsGalois L E] (hodd : Odd (Module.finrank L E))
    (w : NumberField.InfinitePlace E) (hw : w.IsComplex) : (w.comap (algebraMap L E)).IsComplex := by
  haveI := IsUnramifiedAtInfinitePlaces_of_odd_finrank (k := L) (K := E) hodd
  rcases NumberField.InfinitePlace.isUnramified_iff.mp (NumberField.InfinitePlace.isUnramified L w)
    with h | h
  · exact absurd h (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  · exact h

private
theorem isTotallyReal_of_isGalois_of_odd_finrank (K : Type) [Field K] [NumberField K]
    [IsGalois ℚ K] (hodd : Odd (Module.finrank ℚ K)) : NumberField.IsTotallyReal K := by
  haveI := IsUnramifiedAtInfinitePlaces_of_odd_finrank (k := ℚ) (K := K) hodd
  refine ⟨fun w => ?_⟩
  rcases NumberField.InfinitePlace.isUnramified_iff.mp (NumberField.InfinitePlace.isUnramified ℚ w)
    with h | h
  · exact h
  · exact absurd (NumberField.IsTotallyReal.isReal (w.comap (algebraMap ℚ K)))
      (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr h)

private
theorem nrComplexPlaces_eq_zero_of_isGalois_of_odd_finrank (K : Type) [Field K] [NumberField K]
    [IsGalois ℚ K] (hodd : Odd (Module.finrank ℚ K)) :
    NumberField.InfinitePlace.nrComplexPlaces K = 0 :=
  haveI := isTotallyReal_of_isGalois_of_odd_finrank K hodd
  NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K

private
theorem normalClosure_eq_top_of_finrank_eq_two_mul (K E : Type) [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [IsGalois ℚ E] (hKn : ¬ Normal ℚ K)
    (hE : Module.finrank ℚ E = 2 * Module.finrank ℚ K) :
    IntermediateField.normalClosure ℚ K E = ⊤ := by
  haveI := isScalarTower_rat K E
  let ι : K →ₐ[ℚ] E := IsScalarTower.toAlgHom ℚ K E
  have hle : ι.fieldRange ≤ IntermediateField.normalClosure ℚ K E := ι.fieldRange_le_normalClosure
  have e := ((IntermediateField.topEquiv (F := ℚ) (E := K)).symm.trans (IntermediateField.equivMap ⊤ ι)).trans
    (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map ι).symm)
  have hK' : Module.finrank ℚ ι.fieldRange = Module.finrank ℚ K := e.toLinearEquiv.finrank_eq.symm
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hmul : Module.finrank ℚ (IntermediateField.normalClosure ℚ K E) *
      Module.finrank (IntermediateField.normalClosure ℚ K E) E = 2 * Module.finrank ℚ K := by
    rw [Module.finrank_mul_finrank ℚ (IntermediateField.normalClosure ℚ K E) E]
    exact hE
  by_contra hne
  have h2 : 2 ≤ Module.finrank (IntermediateField.normalClosure ℚ K E) E := by
    rcases Nat.lt_or_ge (Module.finrank (IntermediateField.normalClosure ℚ K E) E) 2 with hlt | hge
    · exfalso
      have hb1 : Module.finrank (IntermediateField.normalClosure ℚ K E) E ≠ 1 :=
        fun h1 => hne (IntermediateField.finrank_eq_one_iff_eq_top.mp h1)
      have hb0 : Module.finrank (IntermediateField.normalClosure ℚ K E) E = 0 := by omega
      rw [hb0, mul_zero] at hmul
      omega
    · exact hge
  have hN : Module.finrank ℚ (IntermediateField.normalClosure ℚ K E) ≤ Module.finrank ℚ ι.fieldRange := by
    have h := (Nat.mul_le_mul_left (Module.finrank ℚ (IntermediateField.normalClosure ℚ K E)) h2).trans_eq
      hmul
    rw [hK']
    omega
  have hKN : ι.fieldRange = IntermediateField.normalClosure ℚ K E :=
    IntermediateField.eq_of_le_of_finrank_le hle hN
  exact hKn (Normal.of_algEquiv (h := normalClosure.normal ℚ K E) (e.trans (IntermediateField.equivOfEq hKN)).symm)

private
noncomputable def maximalRealIntermediateField (E : Type) [Field E] [NumberField E] :
    IntermediateField ℚ E :=
  (NumberField.maximalRealSubfield E).toIntermediateField fun q => by
    have h := SubfieldClass.ratCast_mem (NumberField.maximalRealSubfield E) q
    rwa [← eq_ratCast (algebraMap ℚ E) q] at h

private
theorem mem_maximalRealIntermediateField_iff {E : Type} [Field E] [NumberField E] (x : E) :
    x ∈ maximalRealIntermediateField E ↔ x ∈ NumberField.maximalRealSubfield E := by
  rw [← IntermediateField.mem_toSubfield, maximalRealIntermediateField,
    Subfield.toIntermediateField_toSubfield]

private
theorem isTotallyReal_of_normalClosure_eq_top (K E : Type) [Field K] [NumberField K] [Field E]
    [NumberField E] [NumberField.IsTotallyReal K] (htop : IntermediateField.normalClosure ℚ K E = ⊤) :
    NumberField.IsTotallyReal E := by
  have hle : IntermediateField.normalClosure ℚ K E ≤ maximalRealIntermediateField E := by
    rw [normalClosure_le_iff]
    intro f
    rw [SetLike.le_def]
    intro y hy
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    rw [mem_maximalRealIntermediateField_iff, NumberField.mem_maximalRealSubfield_iff]
    intro φ
    rw [RCLike.star_def, ← NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.mp
      (NumberField.IsTotallyReal.complexEmbedding_isReal (φ.comp (f : K →+* E)))) x
  rw [← NumberField.maximalRealSubfield_eq_top_iff_isTotallyReal, eq_top_iff, SetLike.le_def]
  intro x _
  have hx : x ∈ IntermediateField.normalClosure ℚ K E := by
    rw [htop]
    exact IntermediateField.mem_top
  exact (mem_maximalRealIntermediateField_iff x).mp (hle hx)

private
theorem nrRealPlaces_nrComplexPlaces_of_cubic_nonnormal (K L E : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Field E] [NumberField E] [Algebra K E] [Algebra L E] [IsGalois ℚ E]
    (hK : Module.finrank ℚ K = 3) (hKn : ¬ Normal ℚ K) (hL : Module.finrank ℚ L = 2)
    (hE : Module.finrank ℚ E = 6) :
    NumberField.InfinitePlace.nrRealPlaces K = NumberField.InfinitePlace.nrRealPlaces L + 1 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = NumberField.InfinitePlace.nrComplexPlaces L := by
  haveI := isScalarTower_rat K E
  haveI := isScalarTower_rat L E
  have hKr := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hLr := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank L
  rw [hK] at hKr
  rw [hL] at hLr
  by_cases hEr : NumberField.IsTotallyReal E
  · haveI := hEr
    haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.tower_top (K := ℚ) (L := K) (A := E)
    haveI : Algebra.IsAlgebraic L E := Algebra.IsAlgebraic.tower_top (K := ℚ) (L := L) (A := E)
    haveI := NumberField.IsTotallyReal.of_algebra K E
    haveI := NumberField.IsTotallyReal.of_algebra L E
    have hK0 := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K
    have hL0 := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero L
    omega
  · obtain ⟨w, hw⟩ : ∃ w : NumberField.InfinitePlace E, w.IsComplex := by
      by_contra h
      exact hEr ⟨fun w => NumberField.InfinitePlace.not_isComplex_iff_isReal.mp fun hw => h ⟨w, hw⟩⟩
    have hKc : NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
      intro h0
      haveI := NumberField.nrComplexPlaces_eq_zero_iff.mp h0
      haveI := isTotallyReal_of_normalClosure_eq_top K E
        (normalClosure_eq_top_of_finrank_eq_two_mul K E hKn (by omega))
      exact NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw (NumberField.IsTotallyReal.isReal w)
    have hLE : Module.finrank L E = 3 := by
      have h := Module.finrank_mul_finrank ℚ L E
      rw [hL, hE] at h
      omega
    haveI : IsGalois L E := IsGalois.tower_top_of_isGalois ℚ L E
    have hLc : NumberField.InfinitePlace.nrComplexPlaces L ≠ 0 := by
      intro h0
      haveI := NumberField.nrComplexPlaces_eq_zero_iff.mp h0
      exact NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
        (isComplex_comap_of_odd_finrank L E (by rw [hLE]; exact ⟨1, rfl⟩) w hw)
        (NumberField.IsTotallyReal.isReal (w.comap (algebraMap L E)))
    omega

end NumberField.ResolventSignature
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.higherUnitsAt TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt RankinSelberg.primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly TateLocal.exists_hasConductorExponentAt_le_three_of_pow_two_eq_one"
namespace CubicLambda
p2m_export "LanglandsTunnell.CubicLambda" "eulerCoeff zetaEulerPoly resolventSignBit exists_resolventChar zetaEulerPoly_eq_of_resolvent zetaEulerPoly_eq_of_resolvent_of_ramified exists_isFiniteOrderHeckeChar_eulerCoeff_of_isGalois_of_prime_finrank exists_int_jacobiSym_eq_of_finrank_eq_two dirichletChar_neg_one_eq_of_forall_eq_jacobiSym"
namespace CubicResolvent
p2m_open "LanglandsTunnell.CubicLambda LanglandsTunnell"

private theorem ringHom_ringOfIntegers_rat_ext {S : Type} [Ring S] (f g : 𝓞 ℚ →+* S) : f = g := by
  have h : f.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) =
      g.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  ext x
  have hx : x = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) :=
    (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm
  rw [hx]
  exact RingHom.congr_fun h _

private theorem algebra_ringOfIntegers_rat_eq (X : Type) [Field X] [NumberField X] (i : Algebra (𝓞 ℚ) (𝓞 X)) :
    i = NumberField.inst_ringOfIntegersAlgebra ℚ X :=
  Algebra.algebra_ext i (NumberField.inst_ringOfIntegersAlgebra ℚ X) fun r =>
    RingHom.congr_fun (ringHom_ringOfIntegers_rat_ext (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ i)
      (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ X))) r

private theorem isScalarTower_rat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : IsScalarTower ℚ F E :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

private theorem ramificationIdx_eq_one_of_forall_under (L E : Type) [Field L] [NumberField L] [Field E]
    [NumberField E] [Algebra L E] (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : HeightOneSpectrum (𝓞 E)) (h𝔮 : 𝔮.under (𝓞 ℚ) = p)
    (h𝔔 : 𝔔.under (𝓞 L) = 𝔮) : 𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 := by
  haveI : IsScalarTower ℚ L E := isScalarTower_rat L E
  haveI : 𝔮.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal h𝔮).symm⟩
  haveI : 𝔔.asIdeal.LiesOver 𝔮.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal h𝔔).symm⟩
  haveI : 𝔔.asIdeal.LiesOver p.asIdeal := Ideal.LiesOver.trans 𝔔.asIdeal 𝔮.asIdeal p.asIdeal
  have h𝔔p : 𝔔.under (𝓞 ℚ) = p := HeightOneSpectrum.ext (Ideal.over_def 𝔔.asIdeal p.asIdeal).symm
  have he : p.asIdeal.ramificationIdx' 𝔮.asIdeal * 𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 := by
    rw [← Ideal.ramificationIdx_algebra_tower' p.asIdeal 𝔮.asIdeal 𝔔.asIdeal]
    exact hp 𝔔 h𝔔p
  exact Nat.eq_one_of_mul_eq_one_left he

private theorem exists_galoisClosure (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 3)
    (hKn : ¬ Normal ℚ K) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E) (L : Type) (_ : Field L)
      (_ : NumberField L) (_ : Algebra L E),
      IsGalois ℚ E ∧ Module.finrank ℚ E = 6 ∧ Module.finrank ℚ L = 2 := by
  exact
    ⟨NumberField.WildResolventCarrier.GalClosure K, inferInstance, inferInstance, inferInstance,
      NumberField.WildResolventCarrier.resolventField K, inferInstance, inferInstance, inferInstance, inferInstance,
      NumberField.WildResolventCarrier.finrank_galClosure_eq_six_of_not_normal K hK hKn,
      NumberField.WildResolventCarrier.finrank_resolventField K hK hKn⟩

private theorem eulerCoeff_dirichletIdeleChar_eq_apply_natGenerator {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ N) :
    eulerCoeff ℚ χ.dirichletIdeleChar v = χ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ZMod N) := by
  have h : TateGlobal.IsUnramifiedCharAt χ.dirichletIdeleChar v := by
    intro t ht hti
    have h1 : Valued.v (t : v.adicCompletion ℚ) ≤ 1 := ht
    have h2 : Valued.v ((t⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 := hti
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
    have h0 : Valued.v (t : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
    exact DirichletCharacter.dirichletIdeleChar_finIncl_localUnit_of_valued_one χ hv t
      (le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2))
  unfold eulerCoeff
  rw [if_pos h]
  exact DirichletCharacter.coe_dirichletIdeleChar_finIncl_localUnit_of_valued_exp_neg_one χ hv
    (NumberField.AdelicLevel.uniformizerUnit ℚ v) (NumberField.AdelicLevel.valued_uniformizerUnit ℚ v)

private theorem exists_under_eq (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ 𝔮 : HeightOneSpectrum (𝓞 L), 𝔮.under (𝓞 ℚ) = v := by
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) v.asIdeal
    (by rw [RingOfIntegers.ker_algebraMap_eq_bot ℚ L]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, ?_⟩
  · rintro rfl
    exact v.ne_bot (by rw [← hQv]; exact RingOfIntegers.ker_algebraMap_eq_bot ℚ L)
  · exact HeightOneSpectrum.ext hQv

private theorem inertiaDeg_pos_and_le_two (L : Type) [Field L] [NumberField L] (hL : Module.finrank ℚ L = 2)
    (v : HeightOneSpectrum (𝓞 ℚ)) (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : 𝔮.under (𝓞 ℚ) = v) :
    0 < v.asIdeal.inertiaDeg' 𝔮.asIdeal ∧ v.asIdeal.inertiaDeg' 𝔮.asIdeal ≤ 2 := by
  classical
  haveI : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  haveI : 𝔮.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h𝔮]; rfl⟩
  refine ⟨Ideal.inertiaDeg_pos' v.asIdeal 𝔮.asIdeal, ?_⟩
  have hP : 𝔮.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).mpr ⟨‹_›, ‹_›⟩
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) ℚ L v.ne_bot
  rw [← Finset.add_sum_erase _ _ hP, hL] at hsum
  have he : v.asIdeal.ramificationIdx' 𝔮.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver 𝔮.asIdeal v.ne_bot
  exact (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero he)).trans ((Nat.le_add_right _ _).trans_eq hsum)

private theorem dirichletChar_apply_prime_eq_jacobiSym (L : Type) [Field L] [NumberField L]
    (hL : Module.finrank ℚ L = 2) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (d : ℤ)
    (hR : ∀ (ℓ : ℕ), ℓ.Prime → ¬ (ℓ : ℤ) ∣ 2 * d →
        ∀ (p : HeightOneSpectrum (𝓞 ℚ)), (ℓ : 𝓞 ℚ) ∈ p.asIdeal →
          ∀ (𝔮 : HeightOneSpectrum (𝓞 L)), 𝔮.under (𝓞 ℚ) = p →
            p.asIdeal.ramificationIdx' 𝔮.asIdeal = 1 ∧
              (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 → jacobiSym d ℓ = 1) ∧
              (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 → jacobiSym d ℓ = -1))
    (hlaw : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 : HeightOneSpectrum (𝓞 L)), 𝔮.under (𝓞 ℚ) = p →
      (p.asIdeal.ramificationIdx' 𝔮.asIdeal = 1 →
        IsPrimitiveRoot (eulerCoeff ℚ χ.dirichletIdeleChar p) (p.asIdeal.inertiaDeg' 𝔮.asIdeal)) ∧
      (p.asIdeal.ramificationIdx' 𝔮.asIdeal ≠ 1 → eulerCoeff ℚ χ.dirichletIdeleChar p = 0))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ 2 * d.natAbs * N) :
    χ (ℓ : ZMod N) = (jacobiSym d ℓ : ℂ) := by
  obtain ⟨p, hp⟩ : ∃ p : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator p = ℓ :=
    ⟨_, RatIdele.natGenerator_primesEquiv_symm ⟨ℓ, hℓ⟩⟩
  have hℓN : ¬ ℓ ∣ N := fun h => hℓM (Dvd.dvd.mul_left h _)
  have hℓ2d : ¬ ℓ ∣ 2 * d.natAbs := fun h => hℓM (Dvd.dvd.mul_right h _)
  have hℓ2d' : ¬ (ℓ : ℤ) ∣ 2 * d := fun h => hℓ2d (by simpa [Int.natAbs_mul] using Int.ofNat_dvd_left.mp h)
  have hℓp : (ℓ : 𝓞 ℚ) ∈ p.asIdeal := (RatIdele.natCast_mem_asIdeal_iff p ℓ).mpr (by simp [hp])
  obtain ⟨𝔮, h𝔮⟩ := exists_under_eq L p
  obtain ⟨he, hf1, hf2⟩ := hR ℓ hℓ hℓ2d' p hℓp 𝔮 h𝔮
  have hprim := (hlaw p 𝔮 h𝔮).1 he
  rw [eulerCoeff_dirichletIdeleChar_eq_apply_natGenerator χ p (by rw [hp]; exact hℓN), hp] at hprim
  obtain ⟨hf0, hf2'⟩ := inertiaDeg_pos_and_le_two L hL p 𝔮 h𝔮
  rcases (show p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 ∨ p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 by omega) with h | h
  · rw [h] at hprim
    rw [hf1 h, Int.cast_one]
    exact IsPrimitiveRoot.one_right_iff.mp hprim
  · rw [h] at hprim
    rw [hf2 h, Int.cast_neg, Int.cast_one]
    exact IsPrimitiveRoot.eq_neg_one_of_two_right hprim

private theorem dirichletChar_neg_one_eq_sign (L : Type) [Field L] [NumberField L]
    (hL : Module.finrank ℚ L = 2) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hlaw : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 : HeightOneSpectrum (𝓞 L)), 𝔮.under (𝓞 ℚ) = p →
      (p.asIdeal.ramificationIdx' 𝔮.asIdeal = 1 →
        IsPrimitiveRoot (eulerCoeff ℚ χ.dirichletIdeleChar p) (p.asIdeal.inertiaDeg' 𝔮.asIdeal)) ∧
      (p.asIdeal.ramificationIdx' 𝔮.asIdeal ≠ 1 → eulerCoeff ℚ χ.dirichletIdeleChar p = 0)) :
    χ (-1) = if nrComplexPlaces L = 0 then 1 else -1 := by
  obtain ⟨d, hd, hsign, hR⟩ := exists_int_jacobiSym_eq_of_finrank_eq_two L hL
  have hM : 2 * d.natAbs * N ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.mpr hd)) (NeZero.ne N)
  rw [dirichletChar_neg_one_eq_of_forall_eq_jacobiSym χ d (2 * d.natAbs * N) hM
    (fun ℓ hℓ hℓM => dirichletChar_apply_prime_eq_jacobiSym L hL χ d hR hlaw ℓ hℓ hℓM)]
  by_cases h : nrComplexPlaces L = 0
  · rw [if_pos h, if_neg (fun hd' => hsign.mp hd' h)]
  · rw [if_neg h, if_pos (hsign.mpr h)]

end LanglandsTunnell.CubicLambda.CubicResolvent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.higherUnitsAt TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt RankinSelberg.primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly TateLocal.exists_hasConductorExponentAt_le_three_of_pow_two_eq_one"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "inducedCoeff IsBadPlace"
namespace CentralCharacter
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Polynomial NumberField.InfinitePlace NumberField.InfinitePlace.Completion

section Fibre

open LanglandsTunnell.RankinSelberg

variable (F : Type) [Field F] [NumberField F]

private theorem asIdeal_mem_primesOver_of_mem_primeFibre (p : HeightOneSpectrum (𝓞 ℚ))
    {𝔓 : HeightOneSpectrum (𝓞 F)} (h : 𝔓 ∈ primeFibre ℚ F p) :
    𝔓.asIdeal ∈ p.asIdeal.primesOver (𝓞 F) := by
  rw [mem_primeFibre] at h
  refine ⟨𝔓.isPrime, ⟨?_⟩⟩
  rw [← h]
  rfl

private theorem image_asIdeal_primeFibre (p : HeightOneSpectrum (𝓞 ℚ)) :
    HeightOneSpectrum.asIdeal '' primeFibre ℚ F p = p.asIdeal.primesOver (𝓞 F) := by
  ext Q
  constructor
  · rintro ⟨𝔓, h𝔓, rfl⟩
    exact asIdeal_mem_primesOver_of_mem_primeFibre F p h𝔓
  · intro hQ
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver p.asIdeal := hQ.2
    refine ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ⟩, ?_, rfl⟩
    rw [mem_primeFibre]
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def Q p.asIdeal).symm

private theorem primeFibre_finite (p : HeightOneSpectrum (𝓞 ℚ)) :
    (primeFibre ℚ F p).Finite := by
  have hfin : (p.asIdeal.primesOver (𝓞 F)).Finite := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 F)
  rw [← image_asIdeal_primeFibre F p] at hfin
  exact hfin.of_finite_image HeightOneSpectrum.asIdeal_injective.injOn

private theorem finsum_fibre_ramificationIdx_mul_inertiaDeg (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal =
      Module.finrank ℚ F := by
  calc ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal
      = ∑ᶠ Q ∈ HeightOneSpectrum.asIdeal '' primeFibre ℚ F p,
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q :=
        (finsum_mem_image (f := fun Q : Ideal (𝓞 F) => p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q)
          HeightOneSpectrum.asIdeal_injective.injOn).symm
    _ = ∑ᶠ Q ∈ p.asIdeal.primesOver (𝓞 F), p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [image_asIdeal_primeFibre]
    _ = ∑ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 F),
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [← IsDedekindDomain.coe_primesOverFinset p.ne_bot (𝓞 F), finsum_mem_coe_finset]
    _ = Module.finrank ℚ F := Ideal.sum_ramification_inertia (𝓞 F) ℚ F p.ne_bot

end Fibre
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

section SignChar

section

open LanglandsTunnell.RankinSelberg

variable (F : Type) [Field F] [NumberField F]

private theorem inertiaDeg_pos_of_mem_primeFibre (p : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 F))
    (h : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ F p) : 0 < p.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  have hu : 𝔓.under (𝓞 ℚ) = p := h
  haveI : 𝔓.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩
  haveI : p.asIdeal.IsMaximal := p.isMaximal
  exact Ideal.inertiaDeg'_pos p.asIdeal 𝔓.asIdeal

private theorem ramificationIdx_pos_of_mem_primeFibre (p : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 F))
    (h : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ F p) : 0 < p.asIdeal.ramificationIdx' 𝔓.asIdeal := by
  haveI : 𝔓.asIdeal.LiesOver p.asIdeal := (asIdeal_mem_primesOver_of_mem_primeFibre F p h).2
  exact Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver 𝔓.asIdeal p.ne_bot)

private theorem sum_inertiaDeg_eq_three (hF : Module.finrank ℚ F = 3) (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : ∀ 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) :
    ∑ 𝔓 ∈ (primeFibre_finite F p).toFinset, p.asIdeal.inertiaDeg' 𝔓.asIdeal = 3 := by
  rw [← hF, ← finsum_fibre_ramificationIdx_mul_inertiaDeg F p,
    finsum_mem_eq_finite_toFinset_sum _ (primeFibre_finite F p)]
  refine Finset.sum_congr rfl fun 𝔓 h𝔓 => ?_
  rw [hp 𝔓 ((Set.Finite.mem_toFinset _).1 h𝔓), one_mul]

private theorem inducedEulerPoly_eq_prod (c : HeightOneSpectrum (𝓞 F) → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ c p =
      ∏ 𝔓 ∈ (primeFibre_finite F p).toFinset,
        (Polynomial.C 1 - Polynomial.C (c 𝔓) * Polynomial.X ^ p.asIdeal.inertiaDeg' 𝔓.asIdeal : Polynomial ℂ) := by
  rw [LanglandsTunnell.RankinSelberg.inducedEulerPoly, finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite F p)]
  refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
  have hmem : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ F p := (Set.Finite.mem_toFinset _).1 h𝔓
  have hu : 𝔓.under (𝓞 ℚ) = p := hmem
  rw [LanglandsTunnell.RankinSelberg.inducedFactor, hu]

private theorem natDegree_one_sub_C_mul_X_pow_le (a : ℂ) (f : ℕ) :
    (Polynomial.C 1 - Polynomial.C a * Polynomial.X ^ f : Polynomial ℂ).natDegree ≤ f :=
  (Polynomial.natDegree_sub_le _ _).trans
    (max_le ((Polynomial.natDegree_C _).le.trans (Nat.zero_le _)) (Polynomial.natDegree_C_mul_X_pow_le _ _))

private theorem coeff_one_sub_C_mul_X_pow (a : ℂ) {f : ℕ} (hf : 1 ≤ f) :
    (Polynomial.C 1 - Polynomial.C a * Polynomial.X ^ f : Polynomial ℂ).coeff f = -a := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, if_pos rfl, Polynomial.coeff_C, if_neg (by omega)]
  exact zero_sub a

private theorem natDegree_one_sub_X_le : (Polynomial.C 1 - Polynomial.X : Polynomial ℂ).natDegree ≤ 1 :=
  (Polynomial.natDegree_sub_le _ _).trans
    (max_le ((Polynomial.natDegree_C _).le.trans (Nat.zero_le _)) Polynomial.natDegree_X_le)

private theorem coeff_one_one_sub_X : (Polynomial.C 1 - Polynomial.X : Polynomial ℂ).coeff 1 = -1 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C]
  simp

private theorem coeff_prod_one_sub_C_mul_X_pow {ι : Type} (s : Finset ι) (a : ι → ℂ) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 1 ≤ f i) :
    (∏ i ∈ s, (Polynomial.C 1 - Polynomial.C (a i) * Polynomial.X ^ f i : Polynomial ℂ)).coeff (∑ i ∈ s, f i) =
      ∏ i ∈ s, (-a i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro j t hj ih hf
    have h1 : (Polynomial.C 1 - Polynomial.C (a j) * Polynomial.X ^ f j : Polynomial ℂ).natDegree ≤ f j :=
      natDegree_one_sub_C_mul_X_pow_le _ _
    have h2 : (∏ i ∈ t, (Polynomial.C 1 - Polynomial.C (a i) * Polynomial.X ^ f i : Polynomial ℂ)).natDegree ≤
        ∑ i ∈ t, f i :=
      (Polynomial.natDegree_prod_le _ _).trans
        (Finset.sum_le_sum fun i _ => natDegree_one_sub_C_mul_X_pow_le (a i) (f i))
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.prod_insert hj,
      Polynomial.coeff_mul_add_eq_of_natDegree_le h1 h2,
      coeff_one_sub_C_mul_X_pow _ (hf j (Finset.mem_insert_self j t)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private theorem trichotomy_of_sum_eq_three {ι : Type} (s : Finset ι) (f : ι → ℕ) (hpos : ∀ i ∈ s, 1 ≤ f i)
    (hsum : ∑ i ∈ s, f i = 3) :
    ((∀ i ∈ s, f i = 1) ∧
        ∏ i ∈ s, (Polynomial.C 1 - Polynomial.C (1 : ℂ) * Polynomial.X ^ f i : Polynomial ℂ) =
          (Polynomial.C 1 - Polynomial.X) ^ 3 ∧ s.card = 3) ∨
      ((∃ i ∈ s, ∃ j ∈ s, f i = 1 ∧ f j = 2) ∧
        ∏ i ∈ s, (Polynomial.C 1 - Polynomial.C (1 : ℂ) * Polynomial.X ^ f i : Polynomial ℂ) =
          (Polynomial.C 1 - Polynomial.X) * (Polynomial.C 1 - Polynomial.X ^ 2) ∧ s.card = 2) ∨
      ((∀ i ∈ s, f i = 3) ∧
        ∏ i ∈ s, (Polynomial.C 1 - Polynomial.C (1 : ℂ) * Polynomial.X ^ f i : Polynomial ℂ) =
          Polynomial.C 1 - Polynomial.X ^ 3 ∧ s.card = 1) := by
  classical
  have hcard : s.card ≤ 3 := by
    calc s.card = ∑ _i ∈ s, 1 := Finset.card_eq_sum_ones s
      _ ≤ ∑ i ∈ s, f i := Finset.sum_le_sum hpos
      _ = 3 := hsum
  have hcard0 : s.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0, Finset.sum_empty] at hsum
    omega
  rcases (by omega : s.card = 3 ∨ s.card = 2 ∨ s.card = 1) with hc | hc | hc
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hc
    have hsum' := hsum
    have hx_nm : x ∉ ({y, z} : Finset ι) := by simp [hxy, hxz]
    have hy_nm : y ∉ ({z} : Finset ι) := by simp [hyz]
    rw [Finset.sum_insert hx_nm, Finset.sum_insert hy_nm, Finset.sum_singleton] at hsum'
    have hx := hpos x (by simp)
    have hy := hpos y (by simp)
    have hz := hpos z (by simp)
    have hfx : f x = 1 := by omega
    have hfy : f y = 1 := by omega
    have hfz : f z = 1 := by omega
    refine Or.inl ⟨?_, ?_, hc⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact hfx
      · exact hfy
      · exact hfz
    · rw [Finset.prod_insert hx_nm, Finset.prod_insert hy_nm, Finset.prod_singleton,
        hfx, hfy, hfz]
      simp only [map_one, one_mul]
      ring
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
    have hsum' := hsum
    have hx_nm : x ∉ ({y} : Finset ι) := by simp [hxy]
    rw [Finset.sum_insert hx_nm, Finset.sum_singleton] at hsum'
    have hx := hpos x (by simp)
    have hy := hpos y (by simp)
    refine Or.inr (Or.inl ⟨?_, ?_, hc⟩)
    · rcases (by omega : f x = 1 ∧ f y = 2 ∨ f x = 2 ∧ f y = 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨x, by simp, y, by simp, h1, h2⟩
      · exact ⟨y, by simp, x, by simp, h2, h1⟩
    · rw [Finset.prod_insert hx_nm, Finset.prod_singleton]
      rcases (by omega : f x = 1 ∧ f y = 2 ∨ f x = 2 ∧ f y = 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        simp only [map_one, one_mul]
        ring
      · rw [h1, h2]
        simp only [map_one, one_mul]
        ring
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc
    rw [Finset.sum_singleton] at hsum
    refine Or.inr (Or.inr ⟨?_, ?_, hc⟩)
    · intro i hi
      rw [Finset.mem_singleton] at hi
      rw [hi]
      exact hsum
    · rw [Finset.prod_singleton, hsum]
      simp only [map_one, one_mul]

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

private theorem fibre_trichotomy (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 3)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) :
    ((∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal = 1) ∧ zetaEulerPoly K p = (C 1 - X) ^ 3 ∧
        inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p = 1) ∨
      ((∃ 𝔓₁ ∈ primeFibre ℚ K p, ∃ 𝔓₂ ∈ primeFibre ℚ K p,
          p.asIdeal.inertiaDeg' 𝔓₁.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' 𝔓₂.asIdeal = 2) ∧
        zetaEulerPoly K p = (C 1 - X) * (C 1 - X ^ 2) ∧
        inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p = -1) ∨
      ((∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal = 3) ∧ zetaEulerPoly K p = C 1 - X ^ 3 ∧
        inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p = 1) := by
  have hmem : ∀ 𝔓, 𝔓 ∈ (primeFibre_finite K p).toFinset ↔ 𝔓 ∈ primeFibre ℚ K p :=
    fun _ => Set.Finite.mem_toFinset _
  have hpos : ∀ 𝔓 ∈ (primeFibre_finite K p).toFinset, 1 ≤ p.asIdeal.inertiaDeg' 𝔓.asIdeal :=
    fun 𝔓 h𝔓 => inertiaDeg_pos_of_mem_primeFibre K p 𝔓 ((hmem 𝔓).1 h𝔓)
  have hsum := sum_inertiaDeg_eq_three K hK p hp
  have hzeta : zetaEulerPoly K p = ∏ 𝔓 ∈ (primeFibre_finite K p).toFinset,
      (C 1 - C (1 : ℂ) * X ^ p.asIdeal.inertiaDeg' 𝔓.asIdeal) :=
    inducedEulerPoly_eq_prod K (fun _ => (1 : ℂ)) p
  have he3 : inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p =
      -((-1 : ℂ) ^ (primeFibre_finite K p).toFinset.card) := by
    simp only [inducedE3]
    rw [inducedEulerPoly_eq_prod K (fun _ => (1 : ℂ)) p, ← hsum,
      coeff_prod_one_sub_C_mul_X_pow (primeFibre_finite K p).toFinset (fun _ => (1 : ℂ))
        (fun 𝔓 => p.asIdeal.inertiaDeg' 𝔓.asIdeal) hpos,
      Finset.prod_const]
  rcases trichotomy_of_sum_eq_three (primeFibre_finite K p).toFinset (fun 𝔓 => p.asIdeal.inertiaDeg' 𝔓.asIdeal)
      hpos hsum with ⟨h1, hprod, hc⟩ | ⟨h1, hprod, hc⟩ | ⟨h1, hprod, hc⟩
  · refine Or.inl ⟨fun 𝔓 h𝔓 => h1 𝔓 ((hmem 𝔓).2 h𝔓), hzeta.trans hprod, ?_⟩
    rw [he3, hc]
    norm_num
  · obtain ⟨𝔓₁, h₁, 𝔓₂, h₂, hf₁, hf₂⟩ := h1
    refine Or.inr (Or.inl ⟨⟨𝔓₁, (hmem 𝔓₁).1 h₁, 𝔓₂, (hmem 𝔓₂).1 h₂, hf₁, hf₂⟩, hzeta.trans hprod, ?_⟩)
    rw [he3, hc]
    norm_num
  · refine Or.inr (Or.inr ⟨fun 𝔓 h𝔓 => h1 𝔓 ((hmem 𝔓).2 h𝔓), hzeta.trans hprod, ?_⟩)
    rw [he3, hc]
    norm_num

private theorem inducedE3_one_eq_of_eq_mul_inducedEulerPoly (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (L : Type) [Field L] [NumberField L] (hL : Module.finrank ℚ L = 2)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1)
    (c : HeightOneSpectrum (𝓞 L) → ℂ)
    (H3 : ∀ 𝔮 𝔮' : HeightOneSpectrum (𝓞 L), 𝔮.under (𝓞 ℚ) = p → 𝔮'.under (𝓞 ℚ) = p → 𝔮 ≠ 𝔮' →
      c 𝔮' = (c 𝔮)⁻¹)
    (hid : zetaEulerPoly K p = (C 1 - X) * inducedEulerPoly ℚ c p) :
    ∀ 𝔮 : HeightOneSpectrum (𝓞 L), 𝔮.under (𝓞 ℚ) = p →
      p.asIdeal.ramificationIdx' 𝔮.asIdeal = 1 ∧
        (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 →
          inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p = 1) ∧
        (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 →
          inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p = -1) := by
  classical
  have he3 : inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p = 1 ∨
      inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p = -1 := by
    rcases fibre_trichotomy K hK p hp with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  have hne : inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p ≠ 0 := by
    rcases he3 with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  have hc3 : (zetaEulerPoly K p).coeff 3 = -inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p := by
    simp only [inducedE3, zetaEulerPoly]
    ring
  have hcz : (zetaEulerPoly K p).coeff 3 ≠ 0 := by
    rw [hc3]
    exact neg_ne_zero.2 hne
  have hmemL : ∀ 𝔔, 𝔔 ∈ (primeFibre_finite L p).toFinset ↔ 𝔔 ∈ primeFibre ℚ L p :=
    fun _ => Set.Finite.mem_toFinset _
  have hposf : ∀ 𝔔 ∈ (primeFibre_finite L p).toFinset, 1 ≤ p.asIdeal.inertiaDeg' 𝔔.asIdeal :=
    fun 𝔔 h => inertiaDeg_pos_of_mem_primeFibre L p 𝔔 ((hmemL 𝔔).1 h)
  have hpose : ∀ 𝔔 ∈ (primeFibre_finite L p).toFinset, 1 ≤ p.asIdeal.ramificationIdx' 𝔔.asIdeal :=
    fun 𝔔 h => ramificationIdx_pos_of_mem_primeFibre L p 𝔔 ((hmemL 𝔔).1 h)
  have hsumL : ∑ 𝔔 ∈ (primeFibre_finite L p).toFinset,
      p.asIdeal.ramificationIdx' 𝔔.asIdeal * p.asIdeal.inertiaDeg' 𝔔.asIdeal = 2 := by
    have h := finsum_fibre_ramificationIdx_mul_inertiaDeg L p
    rw [hL] at h
    rw [← finsum_mem_eq_finite_toFinset_sum _ (primeFibre_finite L p)]
    exact h
  have hP : inducedEulerPoly ℚ c p = ∏ 𝔔 ∈ (primeFibre_finite L p).toFinset,
      (C 1 - C (c 𝔔) * X ^ p.asIdeal.inertiaDeg' 𝔔.asIdeal) := inducedEulerPoly_eq_prod L c p
  have hdegP : ∀ n : ℕ, (∑ 𝔔 ∈ (primeFibre_finite L p).toFinset, p.asIdeal.inertiaDeg' 𝔔.asIdeal) ≤ n →
      (inducedEulerPoly ℚ c p).natDegree ≤ n := by
    intro n hn
    rw [hP]
    exact (Polynomial.natDegree_prod_le _ _).trans
      ((Finset.sum_le_sum fun 𝔔 _ => natDegree_one_sub_C_mul_X_pow_le (c 𝔔) _).trans hn)

  have hall : ∀ 𝔔 ∈ (primeFibre_finite L p).toFinset, p.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 := by
    intro 𝔔 h𝔔
    by_contra hne1
    have hlt : ∑ 𝔔' ∈ (primeFibre_finite L p).toFinset, p.asIdeal.inertiaDeg' 𝔔'.asIdeal <
        ∑ 𝔔' ∈ (primeFibre_finite L p).toFinset,
          p.asIdeal.ramificationIdx' 𝔔'.asIdeal * p.asIdeal.inertiaDeg' 𝔔'.asIdeal := by
      refine Finset.sum_lt_sum (fun 𝔔' h' => ?_) ⟨𝔔, h𝔔, ?_⟩
      · have h1 := hpose 𝔔' h'
        nlinarith
      · have h1 := hpose 𝔔 h𝔔
        have h2 := hposf 𝔔 h𝔔
        have h3 : 2 ≤ p.asIdeal.ramificationIdx' 𝔔.asIdeal := by omega
        nlinarith
    rw [hsumL] at hlt
    apply hcz
    rw [hid]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc ((C 1 - X) * inducedEulerPoly ℚ c p).natDegree
        ≤ (C 1 - X : Polynomial ℂ).natDegree + (inducedEulerPoly ℚ c p).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + 1 := Nat.add_le_add natDegree_one_sub_X_le (hdegP 1 (by omega))
      _ < 3 := by norm_num

  have hsumf : ∑ 𝔔 ∈ (primeFibre_finite L p).toFinset, p.asIdeal.inertiaDeg' 𝔔.asIdeal = 2 := by
    rw [← hsumL]
    exact Finset.sum_congr rfl fun 𝔔 h𝔔 => by rw [hall 𝔔 h𝔔, one_mul]
  have he3P : inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p =
      ∏ 𝔔 ∈ (primeFibre_finite L p).toFinset, (-c 𝔔) := by
    have h : ((C 1 - X) * inducedEulerPoly ℚ c p).coeff (1 + 2) =
        -inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p := by
      rw [← hid]
      exact hc3
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le natDegree_one_sub_X_le (hdegP 2 hsumf.le), coeff_one_one_sub_X,
      hP, ← hsumf, coeff_prod_one_sub_C_mul_X_pow _ c (fun 𝔔 => p.asIdeal.inertiaDeg' 𝔔.asIdeal) hposf] at h
    linear_combination h
  intro 𝔮 h𝔮p
  have h𝔮 : 𝔮 ∈ (primeFibre_finite L p).toFinset := by
    rw [hmemL, mem_primeFibre]
    exact h𝔮p
  have hcardL : (primeFibre_finite L p).toFinset.card ≤ 2 := by
    calc (primeFibre_finite L p).toFinset.card
        = ∑ _𝔔 ∈ (primeFibre_finite L p).toFinset, 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ 𝔔 ∈ (primeFibre_finite L p).toFinset, p.asIdeal.inertiaDeg' 𝔔.asIdeal := Finset.sum_le_sum hposf
      _ = 2 := hsumf
  have hcard0 : 0 < (primeFibre_finite L p).toFinset.card := Finset.card_pos.2 ⟨𝔮, h𝔮⟩
  refine ⟨hall 𝔮 h𝔮, ?_⟩
  rcases (by omega : (primeFibre_finite L p).toFinset.card = 2 ∨ (primeFibre_finite L p).toFinset.card = 1)
    with hc | hc
  ·
    obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.1 hc
    have hx_nm : x ∉ ({y} : Finset (HeightOneSpectrum (𝓞 L))) := by simp [hxy]
    rw [hs, Finset.sum_insert hx_nm, Finset.sum_singleton] at hsumf
    have hx1 := hposf x (by rw [hs]; simp)
    have hy1 := hposf y (by rw [hs]; simp)
    have hfx : p.asIdeal.inertiaDeg' x.asIdeal = 1 := by omega
    have hfy : p.asIdeal.inertiaDeg' y.asIdeal = 1 := by omega
    rw [hs, Finset.prod_insert hx_nm, Finset.prod_singleton] at he3P
    have hux : x.under (𝓞 ℚ) = p := by
      have hx := (hmemL x).1 (by rw [hs]; simp)
      rwa [mem_primeFibre] at hx
    have huy : y.under (𝓞 ℚ) = p := by
      have hy := (hmemL y).1 (by rw [hs]; simp)
      rwa [mem_primeFibre] at hy
    have hcy : c y = (c x)⁻¹ := H3 x y hux huy hxy
    have hcx : c x ≠ 0 := by
      intro h0
      apply hne
      rw [he3P, h0]
      simp
    have hone : inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p = 1 := by
      rw [he3P, hcy, neg_mul_neg, mul_inv_cancel₀ hcx]
    have h𝔮xy : 𝔮 = x ∨ 𝔮 = y := by
      rw [hs] at h𝔮
      simpa using h𝔮
    refine ⟨fun _ => hone, fun h2 => ?_⟩
    exfalso
    rcases h𝔮xy with h | h
    · rw [h] at h2
      omega
    · rw [h] at h2
      omega
  ·
    obtain ⟨x, hs⟩ := Finset.card_eq_one.1 hc
    rw [hs, Finset.sum_singleton] at hsumf
    rw [hs, Finset.prod_singleton] at he3P
    have h𝔮x : 𝔮 = x := by
      rw [hs] at h𝔮
      simpa using h𝔮
    refine ⟨fun h1 => ?_, fun _ => ?_⟩
    · exfalso
      rw [h𝔮x] at h1
      omega
    · rcases fibre_trichotomy K hK p hp with ⟨-, hz, hK3⟩ | ⟨-, -, hK3⟩ | ⟨-, hz, hK3⟩
      · exfalso
        have hcx : c x = -1 := by linear_combination (-1 : ℂ) * (he3P.symm.trans hK3)
        rw [hid, hP, hs, Finset.prod_singleton, hsumf, hcx] at hz
        have hev := congrArg (Polynomial.eval (-1 : ℂ)) hz
        norm_num at hev
      · exact hK3
      · exfalso
        have hcx : c x = -1 := by linear_combination (-1 : ℂ) * (he3P.symm.trans hK3)
        rw [hid, hP, hs, Finset.prod_singleton, hsumf, hcx] at hz
        have hev := congrArg (Polynomial.eval (-1 : ℂ)) hz
        norm_num at hev

private theorem exists_signChar (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 3) :
    ∃ ε : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, HeckeCharacter.IsFiniteOrderHeckeChar ℚ ε ∧ (∀ x, ε x ^ 2 = 1) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), (∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) →
        IsUnramifiedCharAt ε p ∧
          ((ε (AutomorphicForm.uniformizerIdele ℚ p) : ℂˣ) : ℂ) =
            inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p) ∧
      ∀ v : InfinitePlace ℚ, IsArchCompAt ℚ ε v 0 (nrComplexPlaces K : ℤ) := by
  by_cases hKn : Normal ℚ K
  ·
    haveI : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := hKn }
    obtain ⟨χ, -, -, hlawχ⟩ :=
      exists_isFiniteOrderHeckeChar_eulerCoeff_of_isGalois_of_prime_finrank ℚ K (by rw [hK]; exact Nat.prime_three)
    refine ⟨1, ⟨fun _ => rfl, continuous_const, IsOfFinOrder.one⟩, fun _ => by rw [MonoidHom.one_apply, one_pow],
      fun p hp => ⟨fun _ _ _ => rfl, ?_⟩, fun v x => ?_⟩
    ·
      rw [MonoidHom.one_apply, Units.val_one]
      rcases fibre_trichotomy K hK p hp with ⟨-, -, h3⟩ | ⟨⟨𝔓₁, h𝔓₁, 𝔓₂, h𝔓₂, hf₁, hf₂⟩, -, -⟩ | ⟨-, -, h3⟩
      · exact h3.symm
      · exfalso
        have h1 := (hlawχ p 𝔓₁ h𝔓₁).1 (hp 𝔓₁ h𝔓₁)
        have h2 := (hlawχ p 𝔓₂ h𝔓₂).1 (hp 𝔓₂ h𝔓₂)
        rw [hf₁] at h1
        rw [hf₂] at h2
        exact absurd (h1.unique h2) (by decide)
      · exact h3.symm
    ·
      rw [NumberField.ResolventSignature.nrComplexPlaces_eq_zero_of_isGalois_of_odd_finrank K
        (by rw [hK]; exact ⟨1, rfl⟩)]
      simp only [Nat.cast_zero, zpow_zero, mul_zero, Complex.cpow_zero, mul_one]
      rfl
  ·
    obtain ⟨E, _, _, _, L, _, _, _, hGE, hE, hL⟩ := CubicResolvent.exists_galoisClosure K hK hKn
    haveI := hGE
    haveI : Algebra.IsQuadraticExtension ℚ L := { finrank_eq_two' := hL }
    haveI : IsScalarTower ℚ K E := CubicResolvent.isScalarTower_rat K E
    haveI : IsScalarTower ℚ L E := CubicResolvent.isScalarTower_rat L E
    obtain ⟨θ, -, hlawθ, hinvθ, -, -⟩ := exists_resolventChar K L E hK hKn hL hE
    obtain ⟨ω, hω, hω2, hlawω⟩ :=
      exists_isFiniteOrderHeckeChar_eulerCoeff_of_isGalois_of_prime_finrank ℚ L (by rw [hL]; exact Nat.prime_two)
    obtain ⟨N, _, χ, rfl⟩ := hω.exists_dirichletIdeleChar_eq

    have hid : ∀ p : HeightOneSpectrum (𝓞 ℚ),
        zetaEulerPoly K p = (C 1 - X) * inducedEulerPoly ℚ (eulerCoeff L θ) p := fun p => by
      by_cases hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p → p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1
      · exact zetaEulerPoly_eq_of_resolvent K L E hK hKn hL hE p (eulerCoeff L θ)
          (fun 𝔮 𝔔 h𝔮 h𝔔 => (hlawθ 𝔮 𝔔 h𝔔).1
            (CubicResolvent.ramificationIdx_eq_one_of_forall_under L E p hp 𝔮 𝔔 h𝔮 h𝔔))
          (hinvθ p) hp
      · exact zetaEulerPoly_eq_of_resolvent_of_ramified K L E hK hKn hL hE p (eulerCoeff L θ) hlawθ hp
    have hsign := CubicResolvent.dirichletChar_neg_one_eq_sign L hL χ hlawω
    have hr2 : nrComplexPlaces K = nrComplexPlaces L :=
      (NumberField.ResolventSignature.nrRealPlaces_nrComplexPlaces_of_cubic_nonnormal K L E hK hKn hL hE).2
    refine ⟨χ.dirichletIdeleChar, hω, fun x => by
        have h := DFunLike.congr_fun hω2 x
        rw [MonoidHom.pow_apply, MonoidHom.one_apply, hL] at h
        exact h,
      fun p hp => ?_, fun v => ?_⟩
    ·
      obtain ⟨𝔮, h𝔮⟩ := CubicResolvent.exists_under_eq L p
      obtain ⟨he, hf1, hf2⟩ := inducedE3_one_eq_of_eq_mul_inducedEulerPoly K hK L hL p hp (eulerCoeff L θ)
        (hinvθ p) (hid p) 𝔮 h𝔮
      have hprim := (hlawω p 𝔮 h𝔮).1 he
      obtain ⟨hf0, hfle⟩ := CubicResolvent.inertiaDeg_pos_and_le_two L hL p 𝔮 h𝔮
      have hf12 : p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 ∨ p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 := by omega
      have hval : eulerCoeff ℚ χ.dirichletIdeleChar p = inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p ∧
          eulerCoeff ℚ χ.dirichletIdeleChar p ≠ 0 := by
        rcases hf12 with h | h
        · rw [h] at hprim
          rw [hf1 h]
          have h1 : eulerCoeff ℚ χ.dirichletIdeleChar p = 1 := IsPrimitiveRoot.one_right_iff.mp hprim
          exact ⟨h1, by rw [h1]; exact one_ne_zero⟩
        · rw [h] at hprim
          rw [hf2 h]
          have h1 : eulerCoeff ℚ χ.dirichletIdeleChar p = -1 := hprim.eq_neg_one_of_two_right
          exact ⟨h1, by rw [h1]; exact neg_ne_zero.mpr one_ne_zero⟩
      have hunr : IsUnramifiedCharAt χ.dirichletIdeleChar p := by
        by_contra h
        have hne := hval.2
        unfold eulerCoeff at hne
        rw [if_neg h] at hne
        exact hne rfl
      refine ⟨hunr, ?_⟩
      have h2 := hval.1
      unfold eulerCoeff at h2
      rw [if_pos hunr] at h2
      exact h2
    ·
      have hr2le : nrComplexPlaces L ≤ 1 := by
        have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank L
        rw [hL] at h
        omega
      rw [hr2]
      refine (DirichletArch.isArchCompAt_dirichletIdeleChar_zero_iff χ v _).mpr ?_
      rw [hsign]
      by_cases h0 : nrComplexPlaces L = 0
      · rw [if_pos h0, h0, Nat.cast_zero, zpow_zero]
      · rw [if_neg h0, show nrComplexPlaces L = 1 by omega, Nat.cast_one, zpow_one]

end SignChar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

section CoefficientAlgebra

private theorem inducedE3_eq_inducedE3_one_mul_finprod (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1)
    (c : HeightOneSpectrum (𝓞 K) → ℂ) :
    inducedE3 ℚ c p = inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) p * ∏ᶠ 𝔓 ∈ primeFibre ℚ K p, c 𝔓 := by
  have hmem : ∀ 𝔓, 𝔓 ∈ (primeFibre_finite K p).toFinset ↔ 𝔓 ∈ primeFibre ℚ K p :=
    fun _ => Set.Finite.mem_toFinset _
  have hpos : ∀ 𝔓 ∈ (primeFibre_finite K p).toFinset, 1 ≤ p.asIdeal.inertiaDeg' 𝔓.asIdeal :=
    fun 𝔓 h𝔓 => inertiaDeg_pos_of_mem_primeFibre K p 𝔓 ((hmem 𝔓).1 h𝔓)
  have hsum := sum_inertiaDeg_eq_three K hK p hp
  simp only [inducedE3]
  rw [inducedEulerPoly_eq_prod K c p, inducedEulerPoly_eq_prod K (fun _ => (1 : ℂ)) p, ← hsum,
    coeff_prod_one_sub_C_mul_X_pow _ c (fun 𝔓 => p.asIdeal.inertiaDeg' 𝔓.asIdeal) hpos,
    coeff_prod_one_sub_C_mul_X_pow (primeFibre_finite K p).toFinset (fun _ => (1 : ℂ))
      (fun 𝔓 => p.asIdeal.inertiaDeg' 𝔓.asIdeal) hpos,
    finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite K p), neg_mul, neg_inj, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun 𝔓 _ => (neg_one_mul (c 𝔓)).symm

end CoefficientAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

section Glue

variable (F : Type) [Field F] [NumberField F]

private theorem isUnramifiedCharAt_mul (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F))
    (h₁ : IsUnramifiedCharAt χ₁ v) (h₂ : IsUnramifiedCharAt χ₂ v) : IsUnramifiedCharAt (χ₁ * χ₂) v := by
  intro t ht hti
  have e : localChar (χ₁ * χ₂) v t = localChar χ₁ v t * localChar χ₂ v t := rfl
  rw [e, h₁ t ht hti, h₂ t ht hti, mul_one]

private theorem isAdmissibleTwist_mul (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (h₁ : IsAdmissibleTwist F χ₁)
    (h₂ : IsAdmissibleTwist F χ₂) : IsAdmissibleTwist F (χ₁ * χ₂) := by
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.mul_apply, h₁.1 u, h₂.1 u, mul_one]
  · have hc : Continuous fun x => χ₁ x * χ₂ x := h₁.2.1.mul h₂.2.1
    exact hc
  · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h₁.2.2 x, h₂.2.2 x, mul_one]

private theorem isAdmissibleTwist_of_isFiniteOrderHeckeChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h : HeckeCharacter.IsFiniteOrderHeckeChar F χ) : IsAdmissibleTwist F χ := by
  refine ⟨h.isIdeleClassChar, h.continuous, fun x => ?_⟩
  obtain ⟨n, hn, hχn⟩ := isOfFinOrder_iff_pow_eq_one.mp h.isOfFinOrder
  have hx : ((χ x : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχn, MonoidHom.one_apply, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one hx hn.ne'

private theorem isArchCompAt_mul (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) (u₁ u₂ : ℂ) (a₁ a₂ : ℤ)
    (h₁ : IsArchCompAt F χ₁ w u₁ a₁) (h₂ : IsArchCompAt F χ₂ w u₂ a₂) :
    IsArchCompAt F (χ₁ * χ₂) w (u₁ + u₂) (a₁ + a₂) := by
  intro x
  have hx0 : (x : w.Completion) ≠ 0 := x.ne_zero
  have hn : ((‖(x : w.Completion)‖ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx0)
  have he : extensionEmbedding w (x : w.Completion) / (‖(x : w.Completion)‖ : ℂ) ≠ 0 :=
    div_ne_zero ((_root_.map_ne_zero _).mpr hx0) hn
  have e : archLocalChar (χ₁ * χ₂) w x = archLocalChar χ₁ w x * archLocalChar χ₂ w x := rfl
  rw [e, Units.val_mul, h₁ x, h₂ x, mul_add, Complex.cpow_add _ _ hn, zpow_add₀ he]
  ring

private theorem finsum_isComplex_add_one (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ) :
    (∑ᶠ (w : InfinitePlace F) (hw : w.IsComplex), (kC w hw + 1)) =
      (∑ᶠ (w : InfinitePlace F) (hw : w.IsComplex), kC w hw) + (nrComplexPlaces F : ℤ) := by
  classical
  simp_rw [finsum_eq_dif]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have hsplit : ∀ w : InfinitePlace F, (if hw : w.IsComplex then kC w hw + 1 else 0) =
      (if hw : w.IsComplex then kC w hw else 0) + (if w.IsComplex then (1 : ℤ) else 0) := fun w => by
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun w _ => hsplit w, Finset.sum_add_distrib, Finset.sum_boole]
  congr 1
  rw [nrComplexPlaces, Fintype.card_subtype]

end Glue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

section Restriction

variable (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

private theorem isAdmissibleTwist_comp_genuineβ (hμ : IsAdmissibleTwist K μ) :
    IsAdmissibleTwist ℚ (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom)) := by
  obtain ⟨hμ1, hμc, hμu⟩ := hμ
  refine ⟨fun u => ?_, ?_, fun x => hμu _⟩
  · rw [MonoidHom.comp_apply]
    convert hμ1 (Units.map (algebraMap ℚ K) u) using 2
    apply Units.ext
    simp [M4aHerbrand.Bridge.genuineβ_compat]
  · rw [MonoidHom.coe_comp]
    exact hμc.comp (Continuous.units_map _ (M4aHerbrand.Bridge.continuous_genuineβ ℚ K))

private noncomputable def conormComponent (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (𝔓.adicCompletion K)ˣ :=
  Units.map (NumberField.AdelicLevel.finAdeleEval (𝓞 K) K 𝔓).toMonoidHom
    (Units.map (M4aHerbrand.Bridge.finiteConorm (𝓞 ℚ) ℚ K (𝓞 K)).toMonoidHom x)

private theorem coe_conormComponent (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    ((conormComponent K x 𝔓 : (𝔓.adicCompletion K)ˣ) : 𝔓.adicCompletion K) =
      M4aHerbrand.Bridge.finiteConorm (𝓞 ℚ) ℚ K (𝓞 K) (x : FiniteAdeleRing (𝓞 ℚ) ℚ) 𝔓 :=
  rfl

private theorem valued_conormComponent_localUnit (p : HeightOneSpectrum (𝓞 ℚ)) (a : (p.adicCompletion ℚ)ˣ)
    {𝔓 : HeightOneSpectrum (𝓞 K)} (h𝔓 : 𝔓 ∈ primeFibre ℚ K p) :
    Valued.v ((conormComponent K (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p a) 𝔓 : (𝔓.adicCompletion K)ˣ) :
        𝔓.adicCompletion K) =
      Valued.v (a : p.adicCompletion ℚ) ^ p.asIdeal.ramificationIdx' 𝔓.asIdeal := by
  rw [mem_primeFibre] at h𝔓
  subst h𝔓
  rw [coe_conormComponent, M4aHerbrand.Bridge.finiteConorm_apply]
  refine (HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom ℚ K
    (⟨𝔓, rfl⟩ : (𝔓.under (𝓞 ℚ)).Extension (𝓞 K)) _).trans ?_
  simp only [NumberField.AdelicLevel.localUnit_apply_self]

private theorem map_genuineβ_map_finIncl_localUnit (p : HeightOneSpectrum (𝓞 ℚ)) (a : (p.adicCompletion ℚ)ˣ) :
    Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom
        (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p a)) =
      ∏ 𝔓 ∈ (primeFibre_finite K p).toFinset,
        Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K) (NumberField.AdelicLevel.localUnit (𝓞 K) K 𝔓
          (conormComponent K (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p a) 𝔓)) := by
  apply Units.ext
  rw [Units.coe_prod]
  have hfst : ∀ (s : Finset (HeightOneSpectrum (𝓞 K))) (g : HeightOneSpectrum (𝓞 K) → AdeleRing (𝓞 K) K),
      (∏ 𝔓 ∈ s, g 𝔓).1 = ∏ 𝔓 ∈ s, (g 𝔓).1 := fun s g => _root_.map_prod (NumberField.AdelicLevel.adeleArch (𝓞 K) K) g s
  have hsnd : ∀ (s : Finset (HeightOneSpectrum (𝓞 K))) (g : HeightOneSpectrum (𝓞 K) → AdeleRing (𝓞 K) K),
      (∏ 𝔓 ∈ s, g 𝔓).2 = ∏ 𝔓 ∈ s, (g 𝔓).2 := fun s g => _root_.map_prod (NumberField.AdelicLevel.adeleFin (𝓞 K) K) g s
  refine Prod.ext ?_ ?_
  · rw [hfst]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, M4aHerbrand.Bridge.genuineβ_fst,
      NumberField.AdelicLevel.finIncl_apply_fst, _root_.map_one, Finset.prod_const_one]
  · rw [hsnd]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, M4aHerbrand.Bridge.genuineβ_snd,
      NumberField.AdelicLevel.finIncl_apply_snd]
    refine Subtype.ext (funext fun 𝔔 => ?_)
    have hcomp : ∀ (s : Finset (HeightOneSpectrum (𝓞 K))) (g : HeightOneSpectrum (𝓞 K) → FiniteAdeleRing (𝓞 K) K),
        (∏ 𝔓 ∈ s, g 𝔓) 𝔔 = ∏ 𝔓 ∈ s, g 𝔓 𝔔 :=
      fun s g => _root_.map_prod (NumberField.AdelicLevel.finAdeleEval (𝓞 K) K 𝔔) g s
    show M4aHerbrand.Bridge.finiteConorm (𝓞 ℚ) ℚ K (𝓞 K)
        ((NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p a : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) 𝔔 =
      (∏ 𝔓 ∈ (primeFibre_finite K p).toFinset, ((NumberField.AdelicLevel.localUnit (𝓞 K) K 𝔓
        (conormComponent K (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p a) 𝔓) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K)) 𝔔
    rw [hcomp]
    by_cases h𝔔 : 𝔔 ∈ primeFibre ℚ K p
    · rw [Finset.prod_eq_single 𝔔 (fun 𝔓 _ hne => NumberField.AdelicLevel.localUnit_apply_of_ne _ _ _ _ hne.symm)
        (fun h => absurd ((primeFibre_finite K p).mem_toFinset.2 h𝔔) h), NumberField.AdelicLevel.localUnit_apply_self,
        coe_conormComponent]
    · rw [Finset.prod_eq_one fun 𝔓 h𝔓 => NumberField.AdelicLevel.localUnit_apply_of_ne _ _ _ _ fun h => h𝔔 (by
        rw [h]
        exact (primeFibre_finite K p).mem_toFinset.1 h𝔓)]
      rw [mem_primeFibre] at h𝔔
      rw [M4aHerbrand.Bridge.finiteConorm_apply, NumberField.AdelicLevel.localUnit_apply_of_ne _ _ _ _ h𝔔,
        _root_.map_one]

private theorem isUnramifiedCharAt_comp_genuineβ (p : HeightOneSpectrum (𝓞 ℚ))
    (hμ : ∀ 𝔓 ∈ primeFibre ℚ K p, IsUnramifiedCharAt μ 𝔓) :
    IsUnramifiedCharAt (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom)) p := by
  intro t ht ht'
  show μ (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom
    (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p t))) = 1
  rw [map_genuineβ_map_finIncl_localUnit K p t, _root_.map_prod]
  refine Finset.prod_eq_one fun 𝔓 h𝔓 => ?_
  rw [(primeFibre_finite K p).mem_toFinset] at h𝔓
  have hval := valued_conormComponent_localUnit K p t h𝔓
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht ht'
  rw [Units.val_inv_eq_inv_val, _root_.map_inv₀] at ht'
  have h1 : ((conormComponent K (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p t) 𝔓 : (𝔓.adicCompletion K)ˣ) :
      𝔓.adicCompletion K) ∈ 𝔓.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
    exact pow_le_one' ht _
  have h2 : (((conormComponent K (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p t) 𝔓)⁻¹ : (𝔓.adicCompletion K)ˣ) :
      𝔓.adicCompletion K) ∈ 𝔓.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, _root_.map_inv₀, hval, ← inv_pow]
    exact pow_le_one' ht' _
  exact hμ 𝔓 h𝔓 _ h1 h2

private theorem comp_genuineβ_uniformizerIdele (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1)
    (hμ : ∀ 𝔓 ∈ primeFibre ℚ K p, IsUnramifiedCharAt μ 𝔓) :
    (((μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom)) (AutomorphicForm.uniformizerIdele ℚ p) :
        ℂˣ) : ℂ) =
      ∏ᶠ 𝔓 ∈ primeFibre ℚ K p, inducedCoeff K μ 𝔓 := by
  rw [finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite K p)]
  show ((μ (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom
    (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p
      (NumberField.AdelicLevel.uniformizerUnit ℚ p)))) : ℂˣ) : ℂ) = _
  rw [map_genuineβ_map_finIncl_localUnit K p (NumberField.AdelicLevel.uniformizerUnit ℚ p), _root_.map_prod,
    Units.coe_prod]
  refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
  rw [(primeFibre_finite K p).mem_toFinset] at h𝔓

  have hvc : Valued.v ((conormComponent K (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p
      (NumberField.AdelicLevel.uniformizerUnit ℚ p)) 𝔓 : (𝔓.adicCompletion K)ˣ) : 𝔓.adicCompletion K) =
        WithZero.exp (-1 : ℤ) := by
    rw [valued_conormComponent_localUnit K p _ h𝔓, hp 𝔓 h𝔓, pow_one, NumberField.AdelicLevel.valued_uniformizerUnit]
  generalize conormComponent K (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p
    (NumberField.AdelicLevel.uniformizerUnit ℚ p)) 𝔓 = c at hvc ⊢
  obtain ⟨u, rfl⟩ : ∃ u : (𝔓.adicCompletion K)ˣ, c = NumberField.AdelicLevel.uniformizerUnit K 𝔓 * u :=
    ⟨(NumberField.AdelicLevel.uniformizerUnit K 𝔓)⁻¹ * c, (mul_inv_cancel_left _ _).symm⟩
  rw [Units.val_mul, _root_.map_mul, NumberField.AdelicLevel.valued_uniformizerUnit] at hvc
  have hvu : Valued.v (u : 𝔓.adicCompletion K) = 1 := (mul_eq_left₀ WithZero.exp_ne_zero).1 hvc
  have hu1 : μ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
      (NumberField.AdelicLevel.localUnit (𝓞 K) K 𝔓 u)) = 1 := by
    refine hμ 𝔓 h𝔓 u ?_ ?_
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvu]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, _root_.map_inv₀, hvu, inv_one]
  rw [_root_.map_mul, _root_.map_mul, _root_.map_mul, hu1, mul_one, inducedCoeff, if_pos (hμ 𝔓 h𝔓),
    AutomorphicForm.uniformizerIdele]

section ArchHelpers

open scoped NumberField.LiesOver
p2m_open "NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion M4aHerbrand.ArchSemilocal NumberField.AdelicVolume"

private theorem liesOver_rat (v : InfinitePlace ℚ) (w : InfinitePlace K) : w.1.LiesOver v.1 :=
  liesOver_of_comap_eq (Subsingleton.elim _ _)

private noncomputable def archLift (v : InfinitePlace ℚ) (w : InfinitePlace K) (x : (v.Completion)ˣ) :
    (w.Completion)ˣ :=
  haveI := liesOver_rat K v w
  Units.map (algebraMap v.Completion w.Completion).toMonoidHom x

private theorem coe_archLift (v : InfinitePlace ℚ) (w : InfinitePlace K) (x : (v.Completion)ˣ) :
    haveI := liesOver_rat K v w
    (archLift K v w x : w.Completion) = algebraMap v.Completion w.Completion (x : v.Completion) := rfl

private theorem conorm_archCentralUnit_apply (v : InfinitePlace ℚ) (w : InfinitePlace K)
    (h : w.comap (algebraMap ℚ K) = v) (y : (v.Completion)ˣ) :
    haveI := liesOver_of_comap_eq h
    (genuineInfinitePlaceData (K := ℚ) (L := K)).conorm
        ((archCentralUnit ℚ v y : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 w =
      algebraMap v.Completion w.Completion (y : v.Completion) := by
  subst h
  haveI : w.1.LiesOver (w.comap (algebraMap ℚ K)).1 := liesOver_of_comap_eq rfl
  show psiFactor (w.comap (algebraMap ℚ K)) w
      ((((archCentralUnit ℚ (w.comap (algebraMap ℚ K)) y : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1
        (w.comap (algebraMap ℚ K))) ⊗ₜ[ℚ] (1 : K)) = _
  rw [archCentralUnit_fst_self, psiFactor_tmul, _root_.map_one, mul_one]

private theorem unitsMap_genuineβ_archCentralUnit (v : InfinitePlace ℚ) (x : (v.Completion)ˣ) :
    Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom (archCentralUnit ℚ v x) =
      ∏ w : InfinitePlace K, archCentralUnit K w (archLift K v w x) := by
  classical
  refine Units.ext ?_
  change M4aHerbrand.Bridge.genuineβ ℚ K ((archCentralUnit ℚ v x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) =
    ((∏ w : InfinitePlace K, archCentralUnit K w (archLift K v w x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
  refine Prod.ext ?_ ?_
  ·
    rw [M4aHerbrand.Bridge.genuineβ_fst, Units.coe_prod]
    have h1 : (∏ c : InfinitePlace K, ((archCentralUnit K c (archLift K v c x) : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K)).1 = ∏ c : InfinitePlace K,
          (((archCentralUnit K c (archLift K v c x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 :=
      Prod.fst_prod
    rw [h1]
    funext w
    have h2 : (∏ c : InfinitePlace K, (((archCentralUnit K c (archLift K v c x) : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K)).1) w = ∏ c : InfinitePlace K,
          (((archCentralUnit K c (archLift K v c x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w :=
      Finset.prod_apply w Finset.univ _
    have h3 : (fun c : InfinitePlace K => (((archCentralUnit K c (archLift K v c x) : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K)).1 w) = fun c => (Pi.mulSingle c (archLift K v c x : c.Completion) :
          (d : InfinitePlace K) → d.Completion) w := rfl
    rw [h2, h3, ← Finset.prod_apply w Finset.univ fun c : InfinitePlace K => (Pi.mulSingle c
      (archLift K v c x : c.Completion) : (d : InfinitePlace K) → d.Completion), Finset.univ_prod_mulSingle]
    exact (conorm_archCentralUnit_apply K v w (Subsingleton.elim _ _) x).trans (coe_archLift K v w x).symm
  ·
    rw [M4aHerbrand.Bridge.genuineβ_snd, archCentralUnit_snd, _root_.map_one, Units.coe_prod]
    have h4 : (∏ c : InfinitePlace K, ((archCentralUnit K c (archLift K v c x) : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K)).2 = ∏ c : InfinitePlace K,
          (((archCentralUnit K c (archLift K v c x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 :=
      Prod.snd_prod
    rw [h4]
    symm
    exact Finset.prod_eq_one fun c _ => archCentralUnit_snd c _

private theorem archLocalChar_comp_genuineβ (v : InfinitePlace ℚ) (x : (v.Completion)ˣ) :
    ((archLocalChar (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom)) v x : ℂˣ) : ℂ) =
      ∏ w : InfinitePlace K, ((archLocalChar μ w (archLift K v w x) : ℂˣ) : ℂ) := by
  show ((μ (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom (archCentralUnit ℚ v x)) : ℂˣ) : ℂ) = _
  rw [unitsMap_genuineβ_archCentralUnit, _root_.map_prod, Units.coe_prod]
  rfl

private theorem norm_algebraMap_completion_eq (v : InfinitePlace ℚ) (w : InfinitePlace K) [w.1.LiesOver v.1]
    (y : v.Completion) : ‖algebraMap v.Completion w.Completion y‖ = ‖y‖ := by
  induction y using NumberField.InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (continuous_algebraMap _ _)) continuous_norm
  | ih a =>
    rw [algebraMap_coe, NumberField.InfinitePlace.Completion.norm_coe, NumberField.InfinitePlace.Completion.norm_coe]
    exact (NumberField.InfinitePlace.LiesOver.isometry_algebraMap w v).norm_map_of_map_zero (_root_.map_zero _) a

private theorem norm_archLift (v : InfinitePlace ℚ) (w : InfinitePlace K) (x : (v.Completion)ˣ) :
    ‖(archLift K v w x : w.Completion)‖ = ‖(x : v.Completion)‖ := by
  haveI := liesOver_rat K v w
  rw [coe_archLift]
  exact norm_algebraMap_completion_eq K v w (x : v.Completion)

private theorem extensionEmbedding_archLift (v : InfinitePlace ℚ) (hv : v.IsReal) (w : InfinitePlace K)
    (x : (v.Completion)ˣ) :
    extensionEmbedding w (archLift K v w x : w.Completion) = extensionEmbedding v (x : v.Completion) := by
  haveI := liesOver_rat K v w
  haveI := NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
  rw [coe_archLift]
  exact liesOver_extensionEmbedding_apply w v

private theorem cpow_finset_sum {ι : Type} (s : Finset ι) (b : ℂ) (hb : b ≠ 0) (f : ι → ℂ) :
    b ^ (∑ i ∈ s, f i) = ∏ i ∈ s, b ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, Complex.cpow_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, Complex.cpow_add _ _ hb, ih]

private theorem zpow_finset_sum {ι : Type} (s : Finset ι) (b : ℂ) (hb : b ≠ 0) (f : ι → ℤ) :
    b ^ (∑ i ∈ s, f i) = ∏ i ∈ s, b ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, zpow_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hb, ih]

end ArchHelpers
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

private theorem isArchCompAt_comp_genuineβ
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) (v : InfinitePlace ℚ)
    (hv : v.IsReal) :
    IsArchCompAt ℚ (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom)) v
      ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
      ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), kC w hw)) := by
  classical
  intro x
  have hx0 : (x : v.Completion) ≠ 0 := x.ne_zero
  have hN0 : ((‖(x : v.Completion)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx0)
  have hs0 : extensionEmbedding v (x : v.Completion) / ((‖(x : v.Completion)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero ((_root_.map_ne_zero _).mpr hx0) hN0

  let u : InfinitePlace K → ℂ := fun w => if hw : w.IsReal then uR w hw else uC w (not_isReal_iff_isComplex.mp hw)
  let a : InfinitePlace K → ℤ := fun w =>
    if hw : w.IsReal then ((aR w hw).val : ℤ) else kC w (not_isReal_iff_isComplex.mp hw)

  have hfac : ∀ w : InfinitePlace K, ((archLocalChar μ w (archLift K v w x) : ℂˣ) : ℂ) =
      ((‖(x : v.Completion)‖ : ℝ) : ℂ) ^ ((w.mult : ℂ) * u w) *
        (extensionEmbedding v (x : v.Completion) / ((‖(x : v.Completion)‖ : ℝ) : ℂ)) ^ (a w) := by
    intro w
    by_cases hw : w.IsReal
    · have h := hR w hw (archLift K v w x)
      rw [norm_archLift, extensionEmbedding_archLift K v hv] at h
      rw [h]
      simp only [u, a, dif_pos hw]
    · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
      have h := hC w hw' (archLift K v w x)
      rw [norm_archLift, extensionEmbedding_archLift K v hv] at h
      rw [h]
      simp only [u, a, dif_neg hw]

  have hU : (∑ w : InfinitePlace K, (w.mult : ℂ) * u w) =
      (∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw) := by
    simp_rw [finsum_eq_dif]
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : w.IsReal
    · have hm : w.mult = 1 := mult_isReal ⟨w, hw⟩
      have hc : ¬ w.IsComplex := not_isComplex_iff_isReal.mpr hw
      simp only [u, hm, dif_pos hw, dif_neg hc, Nat.cast_one, one_mul, add_zero]
    · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
      have hm : w.mult = 2 := mult_isComplex ⟨w, hw'⟩
      simp only [u, hm, dif_neg hw, dif_pos hw', Nat.cast_ofNat, zero_add]
  have hA : (∑ w : InfinitePlace K, a w) =
      (∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), kC w hw) := by
    simp_rw [finsum_eq_dif]
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : w.IsReal
    · have hc : ¬ w.IsComplex := not_isComplex_iff_isReal.mpr hw
      simp only [a, dif_pos hw, dif_neg hc, add_zero]
    · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
      simp only [a, dif_neg hw, dif_pos hw', zero_add]

  have hmv : v.mult = 1 := mult_isReal ⟨v, hv⟩
  rw [archLocalChar_comp_genuineβ, Finset.prod_congr rfl fun w _ => hfac w, Finset.prod_mul_distrib,
    ← cpow_finset_sum _ _ hN0, ← zpow_finset_sum _ _ hs0, hU, hA, hmv, Nat.cast_one, one_mul]

end Restriction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

end LanglandsTunnell.CubicInduction.CentralCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField.WildResolventCarrier P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.NumberField"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound.LanglandsTunnell.CubicInduction in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ) :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      (∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1)))) ∧

      ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (M : ℕ),
        (∀ w ∈ primeFibre ℚ K p, ∃ aw : ℕ, aw ≤ M ∧
          LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar μ w) aw) →
        ∃ e : ℕ, e ≤ M + 4 ∧
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ω p) e := by
  obtain rfl := LanglandsTunnell.CubicLambda.CubicResolvent.algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  obtain ⟨ε, hε, hε2, hεp, hεv⟩ := LanglandsTunnell.CubicInduction.CentralCharacter.exists_signChar K hdeg
  refine ⟨μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom) * ε, ?_, ?_, ?_, ?_⟩
  · exact LanglandsTunnell.CubicInduction.CentralCharacter.isAdmissibleTwist_mul ℚ _ _
      (LanglandsTunnell.CubicInduction.CentralCharacter.isAdmissibleTwist_comp_genuineβ K μ hμ)
      (LanglandsTunnell.CubicInduction.CentralCharacter.isAdmissibleTwist_of_isFiniteOrderHeckeChar ℚ ε hε)
  · intro p hp
    have hpK : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1 := fun 𝔓 h𝔓 => by
      by_contra h
      exact hp (Or.inl ⟨𝔓, h𝔓, h⟩)
    have hμK : ∀ 𝔓 ∈ primeFibre ℚ K p, IsUnramifiedCharAt μ 𝔓 := fun 𝔓 h𝔓 => by
      by_contra h
      exact hp (Or.inr ⟨𝔓, h𝔓, h⟩)
    obtain ⟨hεunr, hεval⟩ := hεp p hpK
    have hunr : IsUnramifiedCharAt (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom) * ε) p :=
      LanglandsTunnell.CubicInduction.CentralCharacter.isUnramifiedCharAt_mul ℚ _ _ p
        (LanglandsTunnell.CubicInduction.CentralCharacter.isUnramifiedCharAt_comp_genuineβ K μ p hμK) hεunr
    refine ⟨hunr, ?_⟩
    unfold eulerCoeff
    rw [if_pos hunr, MonoidHom.mul_apply, Units.val_mul,
      LanglandsTunnell.CubicInduction.CentralCharacter.comp_genuineβ_uniformizerIdele K μ p hpK hμK, hεval,
      LanglandsTunnell.CubicInduction.CentralCharacter.inducedE3_eq_inducedE3_one_mul_finprod K hdeg p hpK
        (inducedCoeff K μ), mul_comm]
  · intro uR aR uC kC hR hC v hv
    have h := LanglandsTunnell.CubicInduction.CentralCharacter.isArchCompAt_mul ℚ _ _ v _ _ _ _
      (LanglandsTunnell.CubicInduction.CentralCharacter.isArchCompAt_comp_genuineβ K μ uR aR uC kC hR hC v hv)
      (hεv v)
    rw [add_zero, add_assoc,
      ← LanglandsTunnell.CubicInduction.CentralCharacter.finsum_isComplex_add_one K kC] at h
    exact h

  ·
    intro p M hM
    obtain ⟨e₁, he₁, h₁⟩ :=
      NumberField.TateGlobal.exists_hasConductorExponentAt_localChar_comp_genuineBeta_le K μ p M hM
    obtain ⟨e₂, he₂, h₂⟩ :=
      LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_le_three_of_pow_two_eq_one p
        (NumberField.TateGlobal.localChar ε p) (fun x => hε2 _)
    have hsplit : NumberField.TateGlobal.localChar
        (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom) * ε) p =
        NumberField.TateGlobal.localChar (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom)) p *
          NumberField.TateGlobal.localChar ε p :=
      MonoidHom.ext fun _ => rfl
    have htriv : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (max e₁ e₂),
        NumberField.TateGlobal.localChar
          (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom) * ε) p u = 1 := by
      intro u hu
      rw [hsplit, MonoidHom.mul_apply,
        h₁.1 u (LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p (le_max_left e₁ e₂) hu),
        h₂.1 u (LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p (le_max_right e₁ e₂) hu), one_mul]
    classical
    have hex : ∃ m, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m,
        NumberField.TateGlobal.localChar
          (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom) * ε) p u = 1 := ⟨_, htriv⟩
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun m hm => ?_⟩
    · have := Nat.find_min' hex htriv
      omega
    · have hmin := Nat.find_min hex hm
      push Not at hmin
      exact hmin

end S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound (solution)
