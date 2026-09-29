-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6575abd4-03ff-517a-8d11-e3bd91fc1cef

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd_algebraicClosure
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_of_orderMap
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_jqModC_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "intFormRatiosC_subset x1FunctionField x1FunctionFieldC_le_of_dvd jq coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff jqModC jqModC_rat map_jqModC ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd_algebraicClosure finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange jqModC_mem_intFormRatiosC order_jqModC jqModC_ne_zero"
namespace TowerDescentAux
p2m_open "ModularCurve"

section Const

variable {L : Type*} [Field L]

theorem mem_range_algebraMap_of_isAlgebraic (K : IntermediateField L (LaurentSeries L))
    (t : ↥K) (ht0 : (t : LaurentSeries L) ≠ 0) (ht : 0 < (t : LaurentSeries L).orderTop)
    {y : ↥K} (hy : IsAlgebraic L y) : y ∈ (algebraMap L ↥K).range := by
  classical

  have h_top : ∀ x : ↥K, (x : LaurentSeries L).orderTop = ⊤ ↔ x = 0 := fun x => by
    rw [HahnSeries.orderTop_eq_top, ZeroMemClass.coe_eq_zero]
  have h_mul : ∀ x y : ↥K, ((x * y : ↥K) : LaurentSeries L).orderTop =
      (x : LaurentSeries L).orderTop + (y : LaurentSeries L).orderTop := fun x y => by
    rw [MulMemClass.coe_mul, HahnSeries.orderTop_mul]
  have h_add : ∀ x y : ↥K, min (x : LaurentSeries L).orderTop (y : LaurentSeries L).orderTop ≤
      ((x + y : ↥K) : LaurentSeries L).orderTop := fun x y => by
    rw [AddMemClass.coe_add]
    exact HahnSeries.min_orderTop_le_orderTop_add
  have hcoe : ∀ c : L, ((algebraMap L ↥K c : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) c := fun _ => rfl
  have h_const : ∀ c : L, c ≠ 0 → ((algebraMap L ↥K c : ↥K) : LaurentSeries L).orderTop = 0 := fun c hc => by
    rw [hcoe, algebraMap_laurentSeries_eq_single, HahnSeries.orderTop_single hc]
    rfl
  obtain ⟨P, e, he, -, hord⟩ := Place.exists_of_orderMap (K := L) (F := ↥K)
    (fun f => (f : LaurentSeries L).orderTop) h_top h_mul h_add h_const
    ⟨t, ht, fun h => ht0 (by rw [ZeroMemClass.coe_eq_zero]; exact (h_top t).mp h)⟩

  have hzero : ∀ z : ↥K, IsAlgebraic L z → z ≠ 0 → (z : LaurentSeries L).orderTop = 0 := by
    intro z hz hz0
    rw [hord z hz0, P.ord_eq_zero_of_isAlgebraic hz, mul_zero]
    rfl

  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0, map_zero]⟩
  let c : L := (y : LaurentSeries L).coeff 0
  have hyc : IsAlgebraic L (y - algebraMap L ↥K c) := hy.sub (isAlgebraic_algebraMap c)
  by_cases hz : y - algebraMap L ↥K c = 0
  · exact ⟨c, (sub_eq_zero.mp hz).symm⟩
  exfalso
  have h0 := hzero _ hyc hz

  have hne : ((y - algebraMap L ↥K c : ↥K) : LaurentSeries L) ≠ 0 := fun h => hz ((ZeroMemClass.coe_eq_zero).mp h)
  have hcoeff : ((y - algebraMap L ↥K c : ↥K) : LaurentSeries L).coeff 0 = 0 := by
    rw [AddSubgroupClass.coe_sub, hcoe, algebraMap_laurentSeries_eq_single,
      HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_self]
  have hord0 : ((y - algebraMap L ↥K c : ↥K) : LaurentSeries L).order = 0 := by
    have := HahnSeries.order_eq_orderTop_of_ne_zero hne
    rw [h0] at this
    exact_mod_cast this
  have := mt HahnSeries.coeff_order_eq_zero.mp hne
  rw [hord0] at this
  exact this hcoeff

end Const

section CoeffLift

variable {L : Type*} [Field L] {Ω : Type*} [Field Ω] [Algebra ℚ L] [Algebra ℚ Ω] (τ : L →ₐ[ℚ] Ω)
  (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem coeffMap_coeffEmb' (x : LaurentSeries ℚ) : coeffMap τ.toRingHom (coeffEmb L x) = coeffEmb Ω x := by
  change coeffMap _ (coeffMap _ x) = coeffMap _ x
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_rat _ _) x

theorem coeffMap_algebraMap' (c : L) :
    coeffMap τ.toRingHom (algebraMap L (LaurentSeries L) c) = algebraMap Ω (LaurentSeries Ω) (τ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

theorem coeffMap_mem_laurentBaseChange' {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    coeffMap τ.toRingHom x ∈ laurentBaseChange Ω F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange Ω F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange Ω hz
  | one => simp
  | add _ _ _ _ hx hy => simpa using add_mem hx hy
  | neg _ _ hx => simpa using neg_mem hx
  | inv _ _ hx => simpa using inv_mem hx
  | mul _ _ _ _ hx hy => simpa using mul_mem hx hy

@[reducible] def algebraOfLift : Algebra L ↥(laurentBaseChange Ω F₀) :=
  ((algebraMap Ω ↥(laurentBaseChange Ω F₀)).comp τ.toRingHom).toAlgebra

def liftRingHom : ↥(laurentBaseChange L F₀) →+* ↥(laurentBaseChange Ω F₀) :=
  ((coeffMap τ.toRingHom).comp (laurentBaseChange L F₀).toSubring.subtype).codRestrict
    (laurentBaseChange Ω F₀).toSubring (fun x => coeffMap_mem_laurentBaseChange' τ F₀ x.2)

theorem coe_liftRingHom (x : ↥(laurentBaseChange L F₀)) :
    ((liftRingHom τ F₀ x : ↥(laurentBaseChange Ω F₀)) : LaurentSeries Ω) = coeffMap τ.toRingHom x :=
  rfl

def liftHom : letI := algebraOfLift τ F₀; ↥(laurentBaseChange L F₀) →ₐ[L] ↥(laurentBaseChange Ω F₀) :=
  letI := algebraOfLift τ F₀
  { liftRingHom τ F₀ with
    commutes' := fun c => Subtype.ext (by
      change coeffMap τ.toRingHom (algebraMap L (LaurentSeries L) c) = algebraMap Ω (LaurentSeries Ω) (τ c)
      exact coeffMap_algebraMap' τ c) }

theorem coe_liftHom (x : ↥(laurentBaseChange L F₀)) :
    letI := algebraOfLift τ F₀; ((liftHom τ F₀ x : ↥(laurentBaseChange Ω F₀)) : LaurentSeries Ω) = coeffMap τ.toRingHom x :=
  rfl

theorem liftHom_toRingHom : letI := algebraOfLift τ F₀; (liftHom τ F₀).toRingHom = liftRingHom τ F₀ := rfl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem adjoin_range_algebraMap_eq_top_and_isIntegral [Algebra L Ω] [Algebra.IsAlgebraic L Ω]
    (hτ : algebraMap L Ω = τ.toRingHom) :
    letI := algebraOfLift τ F₀
    letI := (liftRingHom τ F₀).toAlgebra
    Algebra.adjoin ↥(laurentBaseChange L F₀) (Set.range (algebraMap Ω ↥(laurentBaseChange Ω F₀))) = ⊤ ∧
      Algebra.IsIntegral ↥(laurentBaseChange L F₀) ↥(laurentBaseChange Ω F₀) := by
  letI := algebraOfLift τ F₀
  letI algF : Algebra ↥(laurentBaseChange L F₀) ↥(laurentBaseChange Ω F₀) := (liftRingHom τ F₀).toAlgebra
  haveI hST : IsScalarTower L ↥(laurentBaseChange L F₀) ↥(laurentBaseChange Ω F₀) :=
    IsScalarTower.of_algebraMap_eq fun c => ((liftHom τ F₀).commutes c).symm
  haveI : IsScalarTower L Ω ↥(laurentBaseChange Ω F₀) := IsScalarTower.of_algebraMap_eq fun c => by
    change ((algebraMap Ω ↥(laurentBaseChange Ω F₀)).comp τ.toRingHom) c = _
    rw [← hτ]
    rfl

  have hS : ∀ x ∈ Set.range (algebraMap Ω ↥(laurentBaseChange Ω F₀)), IsAlgebraic ↥(laurentBaseChange L F₀) x := by
    rintro _ ⟨c, rfl⟩
    have h : IsAlgebraic L (algebraMap Ω ↥(laurentBaseChange Ω F₀) c) :=
      (Algebra.IsAlgebraic.isAlgebraic (R := L) c).algebraMap
    exact h.tower_top (L := ↥(laurentBaseChange L F₀))

  let T : IntermediateField ↥(laurentBaseChange L F₀) ↥(laurentBaseChange Ω F₀) :=
    IntermediateField.adjoin ↥(laurentBaseChange L F₀) (Set.range (algebraMap Ω ↥(laurentBaseChange Ω F₀)))
  have hT : T = ⊤ := by
    rw [eq_top_iff]
    intro z _

    let T' : Subfield (LaurentSeries Ω) := T.toSubfield.map (laurentBaseChange Ω F₀).toSubfield.subtype
    have hgens : Set.range (algebraMap Ω (LaurentSeries Ω)) ∪ (⇑(coeffEmb Ω) '' (F₀ : Set (LaurentSeries ℚ))) ⊆ T' := by
      rintro w (⟨a, rfl⟩ | ⟨x, hx, rfl⟩)
      · refine ⟨algebraMap Ω ↥(laurentBaseChange Ω F₀) a, ?_, rfl⟩
        exact IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩
      · refine ⟨algebraMap ↥(laurentBaseChange L F₀) ↥(laurentBaseChange Ω F₀) ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩, ?_, ?_⟩
        · exact T.algebraMap_mem _
        · change coeffMap τ.toRingHom (coeffEmb L x) = coeffEmb Ω x
          exact coeffMap_coeffEmb' τ x
    have hle : Subfield.closure (Set.range (algebraMap Ω (LaurentSeries Ω)) ∪
        (⇑(coeffEmb Ω) '' (F₀ : Set (LaurentSeries ℚ)))) ≤ T' := Subfield.closure_le.mpr hgens
    have hz : (z : LaurentSeries Ω) ∈ T' := hle (mem_laurentBaseChange_iff.mp z.2)
    obtain ⟨y, hy, hyz⟩ := hz
    have : y = z := Subtype.ext hyz
    rw [← this]
    exact hy
  refine ⟨?_, ?_⟩
  · rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hS]
    change T.toSubalgebra = ⊤
    rw [hT]
    rfl
  · haveI : Algebra.IsAlgebraic ↥(laurentBaseChange L F₀) ↥T :=
      IntermediateField.isAlgebraic_adjoin fun x hx => (hS x hx).isIntegral
    have halg' : Algebra.IsAlgebraic ↥(laurentBaseChange L F₀) ↥(laurentBaseChange Ω F₀) := by
      constructor
      intro z
      have hz : z ∈ T := by rw [hT]; exact IntermediateField.mem_top
      exact IntermediateField.isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic (⟨z, hz⟩ : ↥T))
    exact Algebra.isAlgebraic_iff_isIntegral.mp halg'

end CoeffLift

section PlaceAlong

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F'] [Algebra K K']
  [Algebra K' F] [Algebra K F] [IsScalarTower K K' F] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

theorem ramificationIndexAlong_restrictScalars_forgetConstants (φ : F →ₐ[K'] F') (w : Place K' F') :
    Place.ramificationIndexAlong (φ.restrictScalars K) (w.forgetConstants (K := K)) = Place.ramificationIndexAlong φ w :=
  rfl

theorem restrictAlong_restrictScalars_forgetConstants (φ : F →ₐ[K'] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K' F') :
    (w.forgetConstants (K := K)).restrictAlong (φ.restrictScalars K) hφ = (w.restrictAlong φ hφ).forgetConstants (K := K) :=
  rfl

end PlaceAlong

section AlongEq

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem ramificationIndexAlong_eq (φ : F →ₐ[K] F') (w : Place K F') :
    Place.ramificationIndexAlong φ w = (letI := φ.toRingHom.toAlgebra; w.ramificationIndex F) :=
  rfl

end AlongEq

section Inclusion

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem isIntegral_inclusion_laurentBaseChange (F : Type) [Field F] [CharZero F] (M N : ℕ) [NeZero M] [NeZero N]
    (hle : ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M) ≤ ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  classical
  let ι : ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)) →ₐ[F] ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) := IntermediateField.inclusion hle
  have hmem : ∀ K : ℕ, coeffEmb F jq ∈ ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField K) := by
    intro K
    apply coeffEmb_mem_laurentBaseChange
    have h := jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 K)
    rw [jqModC_rat] at h
    exact intFormRatiosC_subset ℚ _ h
  let j : ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) := ⟨coeffEmb F jq, hmem N⟩
  let j' : ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)) := ⟨coeffEmb F jq, hmem M⟩
  have hιj' : ι j' = j := Subtype.ext (IntermediateField.coe_inclusion hle j')
  have hT : ∀ K : ℕ, ModularGroup.T ∈ CongruenceSubgroup.Gamma1 K := by
    intro K
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin F ({j} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)))) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 N) (hT N) F (ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) rfl j rfl
  letI algK : Algebra ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) := ι.toRingHom.toAlgebra
  haveI : IsScalarTower F ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) :=
    IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  letI algE : Algebra ↥(IntermediateField.adjoin F ({j'} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)))) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) :=
    (ι.toRingHom.comp (algebraMap ↥(IntermediateField.adjoin F ({j'} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)))) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)))).toAlgebra
  haveI : IsScalarTower ↥(IntermediateField.adjoin F ({j'} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)))) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmap : (IntermediateField.adjoin F ({j'} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)))).map ι =
      IntermediateField.adjoin F ({j} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N))) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, hιj']
  let e₁ : ↥(IntermediateField.adjoin F ({j'} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)))) ≃ₐ[F]
      ↥(IntermediateField.adjoin F ({j} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)))) :=
    (IntermediateField.equivMap (IntermediateField.adjoin F ({j'} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)))) ι).trans
      (IntermediateField.equivOfEq hmap)
  haveI := hFD
  haveI hfinE : Module.Finite ↥(IntermediateField.adjoin F ({j'} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)))) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) :=
    Module.Finite.of_equiv_equiv e₁.symm.toRingEquiv (RingEquiv.refl ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N))) (by
      refine RingHom.ext fun y => ?_
      obtain ⟨z, rfl⟩ := e₁.surjective y
      show ι ((e₁.symm (e₁ z) : ↥(IntermediateField.adjoin F ({j'} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M))))) : ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M))) =
        ((e₁ z : ↥(IntermediateField.adjoin F ({j} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N))))) : ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)))
      rw [e₁.symm_apply_apply]
      rfl)
  haveI : Module.Finite ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) :=
    Module.Finite.of_restrictScalars_finite ↥(IntermediateField.adjoin F ({j'} : Set ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)))) _ _
  haveI : Algebra.IsIntegral ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M)) ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField N)) := Algebra.IsIntegral.of_finite _ _
  exact fun x => Algebra.IsIntegral.isIntegral (R := ↥(ModularCurve.laurentBaseChange F (ModularCurve.x1FunctionField M))) x

end Inclusion

end ModularCurve.TowerDescentAux

open ModularCurve.TowerDescentAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (M N : ℕ) [NeZero M] [NeZero N] (hM : 4 ≤ M) (hMN : M ∣ N)
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (K' : IntermediateField L (LaurentSeries L))
    (hK' : K' = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (hle : K' ≤ K)
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (P : AlgebraicCurve.Place L ↥K) (hP : 0 ≤ P.ord j) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle) P = 1 := by
  classical
  subst hK
  subst hK'

  let τ : L →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI algLΩ : Algebra L (AlgebraicClosure ℚ) := τ.toRingHom.toAlgebra
  have hτ : algebraMap L (AlgebraicClosure ℚ) = τ.toRingHom := rfl
  haveI halgΩ : Algebra.IsAlgebraic L (AlgebraicClosure ℚ) := by
    constructor
    intro x
    obtain ⟨p, hp0, hp⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x
    refine ⟨p.map (algebraMap ℚ L), (Polynomial.map_ne_zero_iff (algebraMap ℚ L).injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      RingHom.ext_rat ((algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap ℚ L)) _]
    exact hp
  haveI : Algebra.IsSeparable L (AlgebraicClosure ℚ) := inferInstance
  letI algN : Algebra L ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N)) := algebraOfLift τ (x1FunctionField N)
  letI algM : Algebra L ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) := algebraOfLift τ (x1FunctionField M)
  haveI : IsScalarTower L (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower L (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let ιL : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) →ₐ[L] ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)) := IntermediateField.inclusion hle
  have hleΩ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M) ≤ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N) :=
    IntermediateField.adjoin.mono (AlgebraicClosure ℚ) _ _ (Set.image_mono (x1FunctionFieldC_le_of_dvd ℚ hMN))
  let ιΩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N)) := IntermediateField.inclusion hleΩ
  let ιΩL : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) →ₐ[L] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N)) := ιΩ.restrictScalars L
  let ΦN : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)) →ₐ[L] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N)) := liftHom τ (x1FunctionField N)
  let ΦM : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) →ₐ[L] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) := liftHom τ (x1FunctionField M)
  have hιLc : ∀ x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)), ((ιL x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) : LaurentSeries L) = (x : LaurentSeries L) :=
    fun x => IntermediateField.coe_inclusion hle x
  have hιΩc : ∀ y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)), ((ιΩ y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N))) : LaurentSeries (AlgebraicClosure ℚ)) = (y : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun y => IntermediateField.coe_inclusion hleΩ y
  have hsq : ΦN.comp ιL = ιΩL.comp ΦM := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply, coe_liftHom, hιLc, hιΩc, coe_liftHom]

  letI algΦN : Algebra ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N)) := (liftRingHom τ (x1FunctionField N)).toAlgebra
  letI algΦM : Algebra ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) := (liftRingHom τ (x1FunctionField M)).toAlgebra
  haveI : IsScalarTower L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N)) := IsScalarTower.of_algebraMap_eq fun c => (ΦN.commutes c).symm
  haveI : IsScalarTower L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) := IsScalarTower.of_algebraMap_eq fun c => (ΦM.commutes c).symm

  obtain ⟨hgenN, hintN⟩ := adjoin_range_algebraMap_eq_top_and_isIntegral τ (x1FunctionField N) hτ
  obtain ⟨hgenM, hintM⟩ := adjoin_range_algebraMap_eq_top_and_isIntegral τ (x1FunctionField M) hτ
  haveI := hintN
  haveI := hintM

  have hjq : coeffEmb L jq = jqModC L := by
    rw [coeffEmb, ← jqModC_rat]
    exact map_jqModC (algebraMap ℚ L)
  have hj0 : (j : LaurentSeries L) ≠ 0 := by rw [hj, hjq]; exact jqModC_ne_zero L
  have hjord : (j : LaurentSeries L).orderTop = (-1 : ℤ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hj0, hj, hjq, order_jqModC]
  have hcoeinv : ∀ (K : IntermediateField L (LaurentSeries L)) (x : ↥K),
      ((x⁻¹ : ↥K) : LaurentSeries L) = (x : LaurentSeries L)⁻¹ := fun _ _ => rfl
  have hjinv : 0 < ((j⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) : LaurentSeries L).orderTop := by
    have hmul : ((j⁻¹ * j : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) : LaurentSeries L).orderTop = 0 := by
      rw [inv_mul_cancel₀ (fun h => hj0 (by rw [h]; rfl)), OneMemClass.coe_one, HahnSeries.orderTop_one]
    rw [MulMemClass.coe_mul, HahnSeries.orderTop_mul, hjord] at hmul

    have hne : ((j⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) : LaurentSeries L).orderTop ≠ ⊤ := by
      rw [ne_eq, HahnSeries.orderTop_eq_top, hcoeinv, inv_eq_zero]; exact hj0
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← ht] at hmul ⊢
    have : t + (-1 : ℤ) = 0 := by exact_mod_cast hmul
    exact_mod_cast (show (0 : ℤ) < t by omega)
  have hjinv0 : ((j⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) : LaurentSeries L) ≠ 0 := by
    rw [hcoeinv, ne_eq, inv_eq_zero]; exact hj0

  have hj'mem : (j : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) := by
    rw [hj]
    apply coeffEmb_mem_laurentBaseChange
    have h := jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 M)
    rw [jqModC_rat] at h
    exact intFormRatiosC_subset ℚ _ h
  let j' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) := ⟨(j : LaurentSeries L), hj'mem⟩
  have hj'inv : 0 < ((j'⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))) : LaurentSeries L).orderTop := by
    rw [hcoeinv]; rw [hcoeinv] at hjinv; exact hjinv
  have hj'inv0 : ((j'⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))) : LaurentSeries L) ≠ 0 := by
    rw [hcoeinv, ne_eq, inv_eq_zero]; exact hj0
  have hconstN : ∀ y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)), IsAlgebraic L y → y ∈ (algebraMap L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))).range :=
    fun y hy => mem_range_algebraMap_of_isAlgebraic _ (j⁻¹) hjinv0 hjinv hy
  have hconstM : ∀ y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)), IsAlgebraic L y → y ∈ (algebraMap L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))).range :=
    fun y hy => mem_range_algebraMap_of_isAlgebraic _ (j'⁻¹) hj'inv0 hj'inv hy

  have hιL : ιL.toRingHom.IsIntegral := isIntegral_inclusion_laurentBaseChange L M N hle
  have hιΩ : ιΩ.toRingHom.IsIntegral := isIntegral_inclusion_laurentBaseChange (AlgebraicClosure ℚ) M N hleΩ
  have hιΩL : ιΩL.toRingHom.IsIntegral := hιΩ
  have hΦN : ΦN.toRingHom.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) x
  have hΦM : ΦM.toRingHom.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))) x

  obtain ⟨W, hW⟩ := Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
    (K := L) (K' := AlgebraicClosure ℚ) (F := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) (F' := ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N))) hgenN hconstN
    (M := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) P
  have e1N : (W.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)) = 1 :=
    Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgenN hconstN W
  let W' : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) := W.restrictAlong ιΩ hιΩ
  have e1M : (W'.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) = 1 :=
    Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgenM hconstM W'

  have hjΩ : ((ΦN j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [coe_liftHom, hj, coeffMap_coeffEmb']
  have hordW : 0 ≤ W.ord (ΦN j) := by
    have h := (W.forgetConstants (K := L)).ord_restrict (F := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) j
    rw [hW, e1N, Place.ord_forgetConstants, RingHom.algebraMap_toAlgebra, Nat.cast_one, one_mul] at h
    rw [← liftHom_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
    rw [h]
    exact hP
  have eΩ : Place.ramificationIndexAlong ιΩ W = 1 :=
    ModularCurve.ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd_algebraicClosure
      M N hM hMN (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField N)) rfl (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) rfl hleΩ (ΦN j) hjΩ W hordW

  have hc1 := Place.ramificationIndexAlong_comp ιL ΦN hιL hΦN
    (RingHom.IsIntegral.trans ιL.toRingHom ΦN.toRingHom hιL hΦN) (W.forgetConstants (K := L))
  have hc2 := Place.ramificationIndexAlong_comp ΦM ιΩL hΦM hιΩL
    (RingHom.IsIntegral.trans ΦM.toRingHom ιΩL.toRingHom hΦM hιΩL) (W.forgetConstants (K := L))
  have d1 : Place.ramificationIndexAlong ΦN (W.forgetConstants (K := L)) =
      (W.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)) := rfl
  have d2 : (W.forgetConstants (K := L)).restrictAlong ΦN hΦN = P := by rw [← hW]; rfl
  have d3 : Place.ramificationIndexAlong ιΩL (W.forgetConstants (K := L)) = Place.ramificationIndexAlong ιΩ W :=
    ramificationIndexAlong_restrictScalars_forgetConstants ιΩ W
  have d4 : (W.forgetConstants (K := L)).restrictAlong ιΩL hιΩL = W'.forgetConstants (K := L) :=
    restrictAlong_restrictScalars_forgetConstants ιΩ hιΩ W
  have d5 : Place.ramificationIndexAlong ΦM (W'.forgetConstants (K := L)) =
      (W'.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) := rfl
  rw [hsq] at hc1
  rw [hc1, d1, e1N, d2, d3, eΩ, d4, d5, e1M, one_mul, mul_one] at hc2
  exact hc2

end
end S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1FunctionField_of_dvd (solution)
