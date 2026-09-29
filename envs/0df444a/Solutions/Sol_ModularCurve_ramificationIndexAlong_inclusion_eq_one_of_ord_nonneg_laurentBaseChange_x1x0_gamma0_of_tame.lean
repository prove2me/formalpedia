-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/00257cdc-c209-5ee8-81d2-7ef63b353603

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame_algebraicClosure
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

namespace P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset qExpFunctionFieldC_mono x1x0FunctionFieldC jq coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff jqModC jqModC_rat map_jqModC ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame_algebraicClosure finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange jqModC_mem_intFormRatiosC order_jqModC jqModC_ne_zero"
namespace FloorDescentAux
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
set_option maxHeartbeats 3200000 in

theorem isIntegral_inclusion
    (L : Type) [Field L]
    (K : IntermediateField L (LaurentSeries L)) (K₁ : IntermediateField L (LaurentSeries L)) (hle : K₁ ≤ K)
    (j : ↥K) (hjK₁ : ((j : LaurentSeries L)) ∈ K₁)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K) :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  classical
  haveI := hFD
  set E := IntermediateField.adjoin L ({j} : Set ↥K) with hE

  have hEK₁ : ∀ x : ↥E, (((x : ↥K) : LaurentSeries L)) ∈ K₁ := by
    have hle' : E ≤ IntermediateField.comap K.val K₁ := by
      rw [hE, IntermediateField.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hjK₁
    intro x
    exact hle' x.2
  let ψ : ↥E →+* ↥K₁ :=
    { toFun := fun x => ⟨((x : ↥K) : LaurentSeries L), hEK₁ x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hψ : (IntermediateField.inclusion hle).toRingHom.comp ψ = algebraMap ↥E ↥K := by
    ext x
    rfl
  intro y
  have hy : IsIntegral ↥E y := Algebra.IsIntegral.isIntegral y
  refine ⟨(minpoly ↥E y).map ψ, (minpoly.monic hy).map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hψ, ← Polynomial.aeval_def, minpoly.aeval]

end Inclusion

end ModularCurve.FloorDescentAux

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame.ModularCurve in
open ModularCurve.FloorDescentAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁)
    (J : ↥K₁) (hJ : ((J : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (x : AlgebraicCurve.Place L ↥K₁) (hx : 0 ≤ x.ord J)
    (h0 : 0 < x.ord J → p % 3 ≠ 1 ∧ (p = 3 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1))
    (h1728 : 0 < x.ord (J - 1728) → p % 4 ≠ 1 ∧ (p = 2 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1)) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle) x = 1 := by
  classical
  subst hK₁
  subst hK₂
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩

  have hΓ : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ≤ CongruenceSubgroup.Gamma0 (M * p) := by
    intro A hA
    obtain ⟨hA1, hA0⟩ := Subgroup.mem_inf.mp hA
    obtain ⟨-, -, h10⟩ := (CongruenceSubgroup.Gamma1_mem _ _).mp hA1
    rw [CongruenceSubgroup.Gamma0_mem] at hA0 ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 hA0 ⊢
    have hcop : IsCoprime (M : ℤ) (p : ℤ) :=
      (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpM)).symm
    push_cast
    exact hcop.mul_dvd h10 hA0
  have hT10 : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      simp [ModularGroup.T]
    · rw [CongruenceSubgroup.Gamma0_mem]
      simp [ModularGroup.T]

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
  letI algN : Algebra L ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) := algebraOfLift τ (x1x0FunctionFieldC ℚ M p)
  letI algM : Algebra L ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := algebraOfLift τ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))
  haveI : IsScalarTower L (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower L (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let ιL : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) →ₐ[L] ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)) := IntermediateField.inclusion hle
  have hleΩ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))) ≤ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p) :=
    IntermediateField.adjoin.mono (AlgebraicClosure ℚ) _ _ (Set.image_mono (qExpFunctionFieldC_mono ℚ hΓ))
  let ιΩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) := IntermediateField.inclusion hleΩ
  let ιΩL : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) →ₐ[L] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) := ιΩ.restrictScalars L
  let ΦN : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)) →ₐ[L] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) := liftHom τ (x1x0FunctionFieldC ℚ M p)
  let ΦM : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) →ₐ[L] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := liftHom τ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))
  have hιLc : ∀ x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))), ((ιL x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))) : LaurentSeries L) = (x : LaurentSeries L) :=
    fun x => IntermediateField.coe_inclusion hle x
  have hιΩc : ∀ y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))), ((ιΩ y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p))) : LaurentSeries (AlgebraicClosure ℚ)) = (y : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun y => IntermediateField.coe_inclusion hleΩ y
  have hsq : ΦN.comp ιL = ιΩL.comp ΦM := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply, coe_liftHom, hιLc, hιΩc, coe_liftHom]

  letI algΦN : Algebra ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) := (liftRingHom τ (x1x0FunctionFieldC ℚ M p)).toAlgebra
  letI algΦM : Algebra ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := (liftRingHom τ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))).toAlgebra
  haveI : IsScalarTower L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) := IsScalarTower.of_algebraMap_eq fun c => (ΦN.commutes c).symm
  haveI : IsScalarTower L ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := IsScalarTower.of_algebraMap_eq fun c => (ΦM.commutes c).symm

  obtain ⟨hgenN, hintN⟩ := adjoin_range_algebraMap_eq_top_and_isIntegral τ (x1x0FunctionFieldC ℚ M p) hτ
  obtain ⟨hgenM, hintM⟩ := adjoin_range_algebraMap_eq_top_and_isIntegral τ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))) hτ
  haveI := hintN
  haveI := hintM

  have hjq : coeffEmb L jq = jqModC L := by
    rw [coeffEmb, ← jqModC_rat]
    exact map_jqModC (algebraMap ℚ L)
  have hj0 : (J : LaurentSeries L) ≠ 0 := by rw [hJ, hjq]; exact jqModC_ne_zero L
  have hjord : (J : LaurentSeries L).orderTop = (-1 : ℤ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hj0, hJ, hjq, order_jqModC]
  have hcoeinv : ∀ (K : IntermediateField L (LaurentSeries L)) (x : ↥K),
      ((x⁻¹ : ↥K) : LaurentSeries L) = (x : LaurentSeries L)⁻¹ := fun _ _ => rfl
  have hjinv : 0 < ((J⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))) : LaurentSeries L).orderTop := by
    have hmul : ((J⁻¹ * J : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))) : LaurentSeries L).orderTop = 0 := by
      rw [inv_mul_cancel₀ (fun h => hj0 (by rw [h]; rfl)), OneMemClass.coe_one, HahnSeries.orderTop_one]
    rw [MulMemClass.coe_mul, HahnSeries.orderTop_mul, hjord] at hmul

    have hne : ((J⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))) : LaurentSeries L).orderTop ≠ ⊤ := by
      rw [ne_eq, HahnSeries.orderTop_eq_top, hcoeinv, inv_eq_zero]; exact hj0
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← ht] at hmul ⊢
    have : t + (-1 : ℤ) = 0 := by exact_mod_cast hmul
    exact_mod_cast (show (0 : ℤ) < t by omega)
  have hjinv0 : ((J⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))) : LaurentSeries L) ≠ 0 := by
    rw [hcoeinv, ne_eq, inv_eq_zero]; exact hj0

  have hJ'mem : (J : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))) := by
    rw [hJ]
    apply coeffEmb_mem_laurentBaseChange
    have h := jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 (M * p))
    rw [jqModC_rat] at h
    exact intFormRatiosC_subset ℚ _ h
  let J' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := ⟨(J : LaurentSeries L), hJ'mem⟩
  have hJ'inv : 0 < ((J'⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))) : LaurentSeries L).orderTop := by
    rw [hcoeinv]; rw [hcoeinv] at hjinv; exact hjinv
  have hJ'inv0 : ((J'⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))) : LaurentSeries L) ≠ 0 := by
    rw [hcoeinv, ne_eq, inv_eq_zero]; exact hj0
  have hconstN : ∀ y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)), IsAlgebraic L y → y ∈ (algebraMap L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))).range :=
    fun y hy => mem_range_algebraMap_of_isAlgebraic _ (J⁻¹) hjinv0 hjinv hy
  have hconstM : ∀ y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))), IsAlgebraic L y → y ∈ (algebraMap L ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))).range :=
    fun y hy => mem_range_algebraMap_of_isAlgebraic _ (J'⁻¹) hJ'inv0 hJ'inv hy

  have hJΩ : ((ΦN J : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [coe_liftHom, hJ, coeffMap_coeffEmb']
  have hJΩmem : ((ΦN J : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))) := by
    rw [hJΩ]
    apply coeffEmb_mem_laurentBaseChange
    have h := jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 (M * p))
    rw [jqModC_rat] at h
    exact intFormRatiosC_subset ℚ _ h
  have hFDL : FiniteDimensional ↥(IntermediateField.adjoin L ({J} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)))) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) hT10 L (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)) rfl J hJ
  have hFDΩ : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({ΦN J} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) hT10 (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) rfl (ΦN J) hJΩ
  have hιL : ιL.toRingHom.IsIntegral := isIntegral_inclusion L _ _ hle J hJ'mem hFDL
  have hιΩ : ιΩ.toRingHom.IsIntegral := isIntegral_inclusion (AlgebraicClosure ℚ) _ _ hleΩ (ΦN J) hJΩmem hFDΩ
  have hιΩL : ιΩL.toRingHom.IsIntegral := hιΩ
  have hΦN : ΦN.toRingHom.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))) x
  have hΦM : ΦM.toRingHom.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))) x

  obtain ⟨W, hW⟩ := Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
    (K := L) (K' := AlgebraicClosure ℚ) (F := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))) (F' := ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p))) hgenN hconstN
    (M := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))) x
  have e1N : (W.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)) = 1 :=
    Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgenN hconstN W
  let W' : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := W.restrictAlong ιΩ hιΩ
  have e1M : (W'.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) = 1 :=
    Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgenM hconstM W'

  have hordeq : ∀ f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)), W.ord (ΦN f) = x.ord f := by
    intro f
    have h := (W.forgetConstants (K := L)).ord_restrict (F := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))) f
    rw [hW, e1N, Place.ord_forgetConstants, RingHom.algebraMap_toAlgebra, Nat.cast_one, one_mul] at h
    rw [← liftHom_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
    exact h
  have hordW : 0 ≤ W.ord (ΦN J) := by rw [hordeq]; exact hx
  have h0Ω : 0 < W.ord (ΦN J) → p % 3 ≠ 1 ∧ (p = 3 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1) := fun h =>
    h0 (by rw [← hordeq]; exact h)
  have h1728Ω : 0 < W.ord (ΦN J - 1728) → p % 4 ≠ 1 ∧ (p = 2 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1) := fun h =>
    h1728 (by rw [← hordeq, map_sub, map_ofNat]; exact h)

  have eΩ : Place.ramificationIndexAlong ιΩ W = 1 :=
    ModularCurve.ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame_algebraicClosure
      p M hM hpM (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M p)) rfl (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) rfl hleΩ (ΦN J) hJΩ W hordW h0Ω h1728Ω

  have hc1 := Place.ramificationIndexAlong_comp ιL ΦN hιL hΦN
    (RingHom.IsIntegral.trans ιL.toRingHom ΦN.toRingHom hιL hΦN) (W.forgetConstants (K := L))
  have hc2 := Place.ramificationIndexAlong_comp ΦM ιΩL hΦM hιΩL
    (RingHom.IsIntegral.trans ΦM.toRingHom ιΩL.toRingHom hΦM hιΩL) (W.forgetConstants (K := L))
  have d1 : Place.ramificationIndexAlong ΦN (W.forgetConstants (K := L)) =
      (W.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)) := rfl
  have d2 : (W.forgetConstants (K := L)).restrictAlong ΦN hΦN = x := by rw [← hW]; rfl
  have d3 : Place.ramificationIndexAlong ιΩL (W.forgetConstants (K := L)) = Place.ramificationIndexAlong ιΩ W :=
    ramificationIndexAlong_restrictScalars_forgetConstants ιΩ W
  have d4 : (W.forgetConstants (K := L)).restrictAlong ιΩL hιΩL = W'.forgetConstants (K := L) :=
    restrictAlong_restrictScalars_forgetConstants ιΩ hιΩ W
  have d5 : Place.ramificationIndexAlong ΦM (W'.forgetConstants (K := L)) =
      (W'.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))) := rfl
  rw [hsq] at hc1
  rw [hc1, d1, e1N, d2, d3, eΩ, d4, d5, e1M, one_mul, mul_one] at hc2
  exact hc2

end
end S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_eq_one_of_ord_nonneg_laurentBaseChange_x1x0_gamma0_of_tame (solution)
