-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.sheetOne_frickeInvolutionBar_separated_and_covering
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a87e25b9-f7e0-517d-8259-90fda755aeb6

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary
import Theorems.Thm_AlgebraicCurve_Place_hasValue_smul_iff
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_sheetOne_frickeInvolutionBar_separated_and_covering
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_sheetOne_frickeInvolutionBar_separated_and_covering.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_sheetOne_frickeInvolutionBar_separated_and_covering.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar ModularPolynomialData coeffEmb modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen_one IsAffineGeomPlace order_jqModC_def jqModC_ne_zero_def charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective modularUnitSeries frickeInvolutionBar frickeInvolutionBar_frickeInvolutionBar isAffineGeomPlace_frobOnPlacesGeomLevel pow_mem_ssJSet_iff mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq frobOnPlacesGeomLevel_charLGeomPlaceOfPoint frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg ord_charLGeomPlaceEquiv_placeInfty_eq_order hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "redFst redSnd d1 hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary reduceFst redFst_frickeInvolutionBar_smul"
namespace SheetOne
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

section Line
variable (k : Type) [Field k]

theorem charLGeomPlaceOfPoint_ne_placeInfty [DecidableEq (RatFunc k)] (c : k) :
    charLGeomPlaceOfPoint k c ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := fun h =>
  RationalFunctionField.placeOfPoint_ne_placeInfty k c ((charLGeomPlaceEquiv k).injective h)

variable [IsAlgClosed k]

theorem exists_eq_charLGeomPlaceOfPoint_or [DecidableEq (RatFunc k)] (Q : Place k ↥(modularFunctionFieldC k 1)) :
    (∃ c : k, Q = charLGeomPlaceOfPoint k c) ∨ Q = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  rcases RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty k ((charLGeomPlaceEquiv k).symm Q) with ⟨c, hc⟩ | h
  · exact Or.inl ⟨c, by rw [charLGeomPlaceOfPoint, ← hc, Equiv.apply_symm_apply]⟩
  · exact Or.inr (by rw [← h, Equiv.apply_symm_apply])

theorem isAffineGeomPlace_iff_ne_placeInfty [DecidableEq (RatFunc k)] (v : Place k ↥(modularFunctionFieldC k 1)) :
    IsAffineGeomPlace k 1 v ↔ v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  have hne0 : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ≠ 0 := fun h0 => jqModC_ne_zero_def k (congrArg Subtype.val h0)
  have hpole : ¬ (jGeomGen k 1 ∈ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).toValuationSubring) := by
    intro hmem
    have hord := (Place.mem_iff_ord_nonneg _ hne0).mp hmem
    rw [ord_charLGeomPlaceEquiv_placeInfty_eq_order] at hord
    have : ((jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) : LaurentSeries k).order = -1 := order_jqModC_def k
    omega
  constructor
  · rintro h rfl
    exact hpole h.1
  · intro hne
    have hmem : jGeomGen k 1 ∈ v.toValuationSubring := by
      by_contra hn
      exact hne (eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
        (lt_of_not_ge ((not_iff_not.mpr (Place.mem_iff_ord_nonneg v hne0)).mp hn)))
    exact ⟨hmem, by rw [jNGeomGen_one]; exact hmem⟩

theorem exists_eq_charLGeomPlaceOfPoint_of_isAffineGeomPlace [DecidableEq (RatFunc k)]
    {v : Place k ↥(modularFunctionFieldC k 1)} (hv : IsAffineGeomPlace k 1 v) : ∃ c : k, v = charLGeomPlaceOfPoint k c :=
  (exists_eq_charLGeomPlaceOfPoint_or k v).resolve_right ((isAffineGeomPlace_iff_ne_placeInfty k v).mp hv)

variable {q : ℕ} [Fact q.Prime] [CharP k q] (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)

theorem frobOnPlacesGeomLevel_injective [DecidableEq (RatFunc k)] :
    Function.Injective (frobOnPlacesGeomLevel k 1 data hKr) := by
  intro x y hxy
  rcases exists_eq_charLGeomPlaceOfPoint_or k x with ⟨a, rfl⟩ | rfl <;>
    rcases exists_eq_charLGeomPlaceOfPoint_or k y with ⟨b, rfl⟩ | rfl
  · rw [frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint] at hxy
    rw [frobenius_inj k q (charLGeomPlaceOfPoint_injective k hxy)]
  · rw [frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty] at hxy
    exact (charLGeomPlaceOfPoint_ne_placeInfty k _ hxy).elim
  · rw [frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty] at hxy
    exact (charLGeomPlaceOfPoint_ne_placeInfty k _ hxy.symm).elim
  · rfl

theorem frob_frob_eq_iff_of_eq_frob [DecidableEq (RatFunc k)] {x y : Place k ↥(modularFunctionFieldC k 1)}
    (h : y = frobOnPlacesGeomLevel k 1 data hKr x) :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr y) = y ↔
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr x) = x := by
  subst h
  exact ⟨fun h => frobOnPlacesGeomLevel_injective k data hKr h, fun h => by rw [h]⟩

theorem mem_ssPlaces_frob_iff [DecidableEq k] [DecidableEq (RatFunc k)] {x : Place k ↥(modularFunctionFieldC k 1)}
    (hx : IsAffineGeomPlace k 1 x) :
    frobOnPlacesGeomLevel k 1 data hKr x ∈ ssPlaces q 1 k ↔ x ∈ ssPlaces q 1 k := by
  haveI : PerfectField k := inferInstance
  obtain ⟨c, rfl⟩ := exists_eq_charLGeomPlaceOfPoint_of_isAffineGeomPlace k hx
  rw [frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq,
    mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq]
  constructor
  · rintro ⟨a, ha, h⟩
    rw [charLGeomPlaceOfPoint_injective k h] at ha
    exact ⟨c, (pow_mem_ssJSet_iff q c).mp ha, rfl⟩
  · rintro ⟨a, ha, h⟩
    rw [← charLGeomPlaceOfPoint_injective k h]
    exact ⟨a ^ q, (pow_mem_ssJSet_iff q a).mpr ha, rfl⟩

end Line

section Transfer

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
  {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
  (P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)

theorem ordFibre_redSnd_of_redFst {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))}
    (hfix : frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) = P.redFst W)
    (haff : IsAffineGeomPlace (ResidueField ↥A) 1 (P.redFst W)) (hss : P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A)) :
    frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
        (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redSnd W)) = P.redSnd W ∧
      IsAffineGeomPlace (ResidueField ↥A) 1 (P.redSnd W) ∧ P.redSnd W ∉ ssPlaces p 1 (ResidueField ↥A) := by
  classical
  rcases P.d1 W with h1 | h1
  ·
    have h1' : P.redFst W = frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redSnd W) := h1
    have hfix2 : frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
        (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redSnd W)) = P.redSnd W :=
      (frob_frob_eq_iff_of_eq_frob (ResidueField ↥A) data hKr h1').mp hfix
    have haff2 : IsAffineGeomPlace (ResidueField ↥A) 1 (P.redSnd W) := by

      rw [isAffineGeomPlace_iff_ne_placeInfty] at haff ⊢
      intro h
      apply haff
      rw [h1', h, frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty]
    refine ⟨hfix2, haff2, fun h => hss ?_⟩
    rw [h1']
    exact (mem_ssPlaces_frob_iff (ResidueField ↥A) data hKr haff2).mpr h
  ·
    have h1' : P.redSnd W = frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W) := h1.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [h1', hfix]
    · rw [h1']; exact isAffineGeomPlace_frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr _ haff
    · rw [h1']; exact fun h => hss ((mem_ssPlaces_frob_iff (ResidueField ↥A) data hKr haff).mp h)

end Transfer

end ModularCurve.PlaceSpecialization.SheetOne

open ModularCurve.PlaceSpecialization.SheetOne in

theorem solution
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (u : ↥(modularFunctionFieldBar (1 * p)))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p)) :
    (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      W ∈ {W | ((frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) = P.redFst W ∧
        IsAffineGeomPlace (ResidueField ↥A) 1 (P.redFst W) ∧ P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A)) ∧
        (∃ a : ↥A, IsLocalRing.residue ↥A a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))} →
      frickeInvolutionBar (1 * p) • W ∉ {W | ((frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) = P.redFst W ∧
        IsAffineGeomPlace (ResidueField ↥A) 1 (P.redFst W) ∧ P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A)) ∧
        (∃ a : ↥A, IsLocalRing.residue ↥A a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))}) ∧
    (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
          (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) = P.redFst W →
      IsAffineGeomPlace (ResidueField ↥A) 1 (P.redFst W) → P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A) →
      W ∈ {W | ((frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) = P.redFst W ∧
        IsAffineGeomPlace (ResidueField ↥A) 1 (P.redFst W) ∧ P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A)) ∧
        (∃ a : ↥A, IsLocalRing.residue ↥A a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))} ∨
      frickeInvolutionBar (1 * p) • W ∈ {W | ((frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) = P.redFst W ∧
        IsAffineGeomPlace (ResidueField ↥A) 1 (P.redFst W) ∧ P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A)) ∧
        (∃ a : ↥A, IsLocalRing.residue ↥A a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))}) := by
  classical
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)

  have hww : ∀ g : ↥(modularFunctionFieldBar (1 * p)), frickeInvolutionBar (1 * p) (frickeInvolutionBar (1 * p) g) = g :=
    frickeInvolutionBar_frickeInvolutionBar (1 * p)
  have hval : ∀ (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (a : AlgebraicClosure ℚ),
      (frickeInvolutionBar (1 * p) • W).HasValue u a ↔ W.HasValue (frickeInvolutionBar (1 * p) u) a := by
    intro W a
    have h := Place.hasValue_smul_iff (frickeInvolutionBar (1 * p)) W (frickeInvolutionBar (1 * p) u) a
    rwa [hww] at h

  have hsep : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
          (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) = P.redFst W →
      IsAffineGeomPlace (ResidueField ↥A) 1 (P.redFst W) → P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A) →
      ((∃ a : ↥A, IsLocalRing.residue ↥A a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)) ∨
        (∃ a : ↥A, IsLocalRing.residue ↥A a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * p) u) (a : AlgebraicClosure ℚ))) ∧
      ¬ ((∃ a : ↥A, IsLocalRing.residue ↥A a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)) ∧
        (∃ a : ↥A, IsLocalRing.residue ↥A a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * p) u) (a : AlgebraicClosure ℚ))) :=
    fun W hfix haff hss => hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary P u hu W hfix haff hss
  refine ⟨?_, ?_⟩
  ·
    rintro W ⟨⟨hfix, haff, hss⟩, a, ha, hWa⟩ ⟨-, b, hb, hWb⟩
    exact (hsep W hfix haff hss).2 ⟨⟨a, ha, hWa⟩, ⟨b, hb, (hval W b).mp hWb⟩⟩
  ·
    intro W hfix haff hss
    rcases (hsep W hfix haff hss).1 with ⟨a, ha, hWa⟩ | ⟨a, ha, hWa⟩
    · exact Or.inl ⟨⟨hfix, haff, hss⟩, a, ha, hWa⟩
    · refine Or.inr ⟨?_, a, ha, (hval W a).mpr hWa⟩
      have hred : P.redFst (frickeInvolutionBar (1 * p) • W) = P.redSnd W := redFst_frickeInvolutionBar_smul P W
      rw [hred]
      exact ordFibre_redSnd_of_redFst P hfix haff hss

end S_ModularCurve_PlaceSpecialization_sheetOne_frickeInvolutionBar_separated_and_covering
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_sheetOne_frickeInvolutionBar_separated_and_covering (solution)
