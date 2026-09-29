-- Prove2me | solution 1 for ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c6fdba14-e330-5c88-9646-4fc990448739

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_of_orderMap
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_jqModC_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH_of_eq_two
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH_of_eq_two.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset qExpFunctionFieldC_mono jq coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff translation_mem_GammaH Gamma1_le_GammaH xHFunctionField FullLevel.levelH jqModC jqModC_rat map_jqModC ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange jqModC_mem_intFormRatiosC order_jqModC jqModC_ne_zero"
namespace HramXHDescentAux
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

section PlaceLemmas

variable {Ω : Type*} {F : Type*} [Field Ω] [Field F] [Algebra Ω F]

theorem mem_of_ord_nonneg' (v : Place Ω F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  by_cases hf : f = 0
  · rw [hf]; exact v.toValuationSubring.zero_mem
  · exact v.mem_of_ord_nonneg hf h

theorem inv_mem_of_ord_le_zero (v : Place Ω F) {f : F} (hf : f ≠ 0) (h : v.ord f ≤ 0) :
    f⁻¹ ∈ v.toValuationSubring :=
  v.mem_of_ord_nonneg (inv_ne_zero hf) (by rw [v.ord_inv]; linarith)

theorem exists_ord_sub_algebraMap_pos [IsAlgClosed Ω] (v : Place Ω F) (t : F)
    [Algebra.IsAlgebraic ↥(IntermediateField.adjoin Ω ({t} : Set F)) F] (ht : 0 ≤ v.ord t) :
    ∃ a : Ω, 0 < v.ord (t - algebraMap Ω F a) := by
  by_contra hcon
  push Not at hcon
  have htO : t ∈ v.toValuationSubring := mem_of_ord_nonneg' v ht

  let Ov : Subalgebra Ω F :=
    { v.toValuationSubring.toSubring with
      algebraMap_mem' := v.algebraMap_mem' }
  have hOv : ∀ x, x ∈ Ov ↔ x ∈ v.toValuationSubring := fun _ => Iff.rfl
  have haeval : ∀ r : Polynomial Ω, Polynomial.aeval t r ∈ v.toValuationSubring := by
    intro r
    have : Polynomial.aeval t r = Ov.val (Polynomial.aeval (⟨t, htO⟩ : ↥Ov) r) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    rw [this]
    exact (Polynomial.aeval (⟨t, htO⟩ : ↥Ov) r).2

  have hpoly : ∀ (n : ℕ) (p : Polynomial Ω), p.natDegree = n → p ≠ 0 →
      (Polynomial.aeval t p)⁻¹ ∈ v.toValuationSubring := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hn hp0
      by_cases hdeg : p.natDegree = 0
      · obtain ⟨c, rfl⟩ : ∃ c, p = Polynomial.C c := ⟨_, Polynomial.eq_C_of_natDegree_eq_zero hdeg⟩
        rw [Polynomial.aeval_C, ← map_inv₀]
        exact v.algebraMap_mem' _
      · have hdeg' : p.degree ≠ 0 := fun h => hdeg (Polynomial.natDegree_eq_of_degree_eq_some h)
        obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg'
        have hsplit : (Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a)) = p :=
          Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
        have hq0 : p /ₘ (Polynomial.X - Polynomial.C a) ≠ 0 := by
          intro h0; apply hp0; rw [← hsplit, h0, mul_zero]
        have hqdeg : (p /ₘ (Polynomial.X - Polynomial.C a)).natDegree < n := by
          rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C a), Polynomial.natDegree_X_sub_C, ← hn]
          omega
        rw [← hsplit, map_mul, mul_inv]
        refine mul_mem ?_ (ih _ hqdeg _ rfl hq0)
        rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
        by_cases h0 : t - algebraMap Ω F a = 0
        · rw [h0, inv_zero]; exact zero_mem _
        · exact inv_mem_of_ord_le_zero v h0 (hcon a)

  have hadj : ∀ x ∈ IntermediateField.adjoin Ω ({t} : Set F), x ∈ v.toValuationSubring := by
    intro x hx
    rw [IntermediateField.mem_adjoin_simple_iff] at hx
    obtain ⟨r, s, rfl⟩ := hx
    by_cases hs : s = 0
    · rw [hs, map_zero, div_zero]; exact zero_mem _
    · rw [div_eq_mul_inv]
      exact mul_mem (haeval r) (hpoly _ s rfl hs)

  have hall : ∀ x : F, x ∈ v.toValuationSubring := by
    intro x
    have hx : IsIntegral ↥(IntermediateField.adjoin Ω ({t} : Set F)) x :=
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    let φ : ↥(IntermediateField.adjoin Ω ({t} : Set F)) →+* ↥v.toValuationSubring :=
      { toFun := fun r => ⟨r, hadj r r.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hxV : IsIntegral ↥v.toValuationSubring x := hx.map_of_comp_eq φ (RingHom.id F) (by ext; rfl)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxV
    rw [← hy]
    exact y.2
  exact v.ne_top' (SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => hall x⟩)

end PlaceLemmas

section CoreBar

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem coreBar
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (K : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hK : K = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))
    (K₀ : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle : K₀ ≤ K)
    (j : ↥K) (hj : ((j : LaurentSeries (AlgebraicClosure ℚ))) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq)
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥K) (hP0 : P.ord j = 0) (hP1728 : P.ord (j - 1728) = 0) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle) P = 1 := by
  classical
  subst hK
  subst hK₀
  haveI : NeZero (q ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
  have hTH : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') := ModularCurve.translation_mem_GammaH _ _
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]

  let ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := IntermediateField.inclusion hle
  have hjq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
    rw [coeffEmb, ← jqModC_rat]
    exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  have hj'mem : coeffEmb (AlgebraicClosure ℚ) jq ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    apply coeffEmb_mem_laurentBaseChange
    have h := jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 M')
    rw [jqModC_rat] at h
    exact intFormRatiosC_subset ℚ _ h
  let j' : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := ⟨coeffEmb (AlgebraicClosure ℚ) jq, hj'mem⟩
  have hιj' : ι j' = j := Subtype.ext hj.symm
  have hyK : ((j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := hj.trans hjq

  have hFD : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hTH (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) rfl j hj
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 M') hT0 (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) rfl j' rfl

  have hjK₀ : ((j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    rw [hj]; exact hj'mem
  have hι : ι.toRingHom.IsIntegral := isIntegral_inclusion (AlgebraicClosure ℚ) _ _ hle j hjK₀ hFD

  obtain ⟨-, -, hubgen⟩ :=
    ModularCurve.ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
      (q ^ 2 * M') (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) (ModularCurve.Gamma1_le_GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) j hyK P

  have he1 : 1 ≤ Place.ramificationIndexAlong ι P := Place.one_le_ramificationIndexAlong ι hι P
  have hord : ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))), P.ord (ι f) =
      (Place.ramificationIndexAlong ι P : ℤ) * (P.restrictAlong ι hι).ord f :=
    fun f => Place.ord_restrictAlong ι hι P f
  have he1' : (1 : ℤ) ≤ (Place.ramificationIndexAlong ι P : ℤ) := by exact_mod_cast he1

  have hP' : (P.restrictAlong ι hι).ord j' = 0 := by
    have h := hord j'
    rw [hιj', hP0] at h
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exfalso; linarith
    · exact h1

  haveI := hFD'
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j'} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨a, ha⟩ := exists_ord_sub_algebraMap_pos (P.restrictAlong ι hι) j' hP'.symm.le
  have hkey := hord (j' - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) a)
  rw [map_sub, hιj', AlgHom.commutes] at hkey

  rcases eq_or_ne a 0 with rfl | ha0
  · exfalso
    simp only [map_zero, sub_zero] at ha
    rw [hP'] at ha
    exact lt_irrefl _ ha
  rcases eq_or_ne a 1728 with rfl | ha1728
  · exfalso
    have h1728K : algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) 1728 = 1728 := map_ofNat _ 1728
    have h1728K' : algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) 1728 = 1728 := map_ofNat _ 1728
    rw [h1728K'] at ha hkey
    rw [h1728K, hP1728] at hkey
    have : (0 : ℤ) < (Place.ramificationIndexAlong ι P : ℤ) * (P.restrictAlong ι hι).ord (j' - 1728) :=
      mul_pos (by linarith) ha
    rw [← hkey] at this
    exact lt_irrefl _ this
  have h1 : P.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) a) ≤ 1 := hubgen a ha0 ha1728
  rw [hkey] at h1
  suffices hle1 : (Place.ramificationIndexAlong ι P : ℤ) ≤ 1 by
    have : Place.ramificationIndexAlong ι P ≤ 1 := by exact_mod_cast hle1
    exact le_antisymm this he1
  nlinarith

end CoreBar

end ModularCurve.HramXHDescentAux

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH_of_eq_two.ModularCurve in
open ModularCurve.HramXHDescentAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle : K₀ ≤ K)
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (P : AlgebraicCurve.Place L ↥K) (hP0 : P.ord j = 0) (hP1728 : P.ord (j - 1728) = 0) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle) P = 1 := by
  classical
  have hK' : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) := hK
  subst hK'
  subst hK₀
  clear hK
  haveI : NeZero (q ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))

  have hΓ : CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ≤ CongruenceSubgroup.Gamma0 M' := by
    intro A hA
    have hA0 : A ∈ CongruenceSubgroup.Gamma0 (q ^ 2 * M') := CohCarrier.GammaH_le_Gamma0 _ hA
    rw [CongruenceSubgroup.Gamma0_mem] at hA0 ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hA0 ⊢
    push_cast at hA0
    exact (dvd_mul_left (M' : ℤ) ((q : ℤ) ^ 2)).trans hA0
  have hTH : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') := ModularCurve.translation_mem_GammaH _ _

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
  letI algN : Algebra L ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := algebraOfLift τ (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
  letI algM : Algebra L ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := algebraOfLift τ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))
  haveI : IsScalarTower L (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower L (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let ιL : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) →ₐ[L] ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := IntermediateField.inclusion hle
  have hleΩ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ≤ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :=
    IntermediateField.adjoin.mono (AlgebraicClosure ℚ) _ _ (Set.image_mono (qExpFunctionFieldC_mono ℚ hΓ))
  let ιΩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := IntermediateField.inclusion hleΩ
  let ιΩL : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) →ₐ[L] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := ιΩ.restrictScalars L
  let ΦN : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) →ₐ[L] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := liftHom τ (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
  let ΦM : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) →ₐ[L] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := liftHom τ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))
  have hιLc : ∀ x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))), ((ιL x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries L) = (x : LaurentSeries L) :=
    fun x => IntermediateField.coe_inclusion hle x
  have hιΩc : ∀ y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))), ((ιΩ y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries (AlgebraicClosure ℚ)) = (y : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun y => IntermediateField.coe_inclusion hleΩ y
  have hsq : ΦN.comp ιL = ιΩL.comp ΦM := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply, coe_liftHom, hιLc, hιΩc, coe_liftHom]

  letI algΦN : Algebra ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := (liftRingHom τ (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))).toAlgebra
  letI algΦM : Algebra ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := (liftRingHom τ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))).toAlgebra
  haveI : IsScalarTower L ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := IsScalarTower.of_algebraMap_eq fun c => (ΦN.commutes c).symm
  haveI : IsScalarTower L ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := IsScalarTower.of_algebraMap_eq fun c => (ΦM.commutes c).symm

  obtain ⟨hgenN, hintN⟩ := adjoin_range_algebraMap_eq_top_and_isIntegral τ (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) hτ
  obtain ⟨hgenM, hintM⟩ := adjoin_range_algebraMap_eq_top_and_isIntegral τ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) hτ
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
  have hjinv : 0 < ((j⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries L).orderTop := by
    have hmul : ((j⁻¹ * j : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries L).orderTop = 0 := by
      rw [inv_mul_cancel₀ (fun h => hj0 (by rw [h]; rfl)), OneMemClass.coe_one, HahnSeries.orderTop_one]
    rw [MulMemClass.coe_mul, HahnSeries.orderTop_mul, hjord] at hmul

    have hne : ((j⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries L).orderTop ≠ ⊤ := by
      rw [ne_eq, HahnSeries.orderTop_eq_top, hcoeinv, inv_eq_zero]; exact hj0
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← ht] at hmul ⊢
    have : t + (-1 : ℤ) = 0 := by exact_mod_cast hmul
    exact_mod_cast (show (0 : ℤ) < t by omega)
  have hjinv0 : ((j⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries L) ≠ 0 := by
    rw [hcoeinv, ne_eq, inv_eq_zero]; exact hj0

  have hj'mem : (j : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    rw [hj]
    apply coeffEmb_mem_laurentBaseChange
    have h := jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 M')
    rw [jqModC_rat] at h
    exact intFormRatiosC_subset ℚ _ h
  let j' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := ⟨(j : LaurentSeries L), hj'mem⟩
  have hj'inv : 0 < ((j'⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))) : LaurentSeries L).orderTop := by
    rw [hcoeinv]; rw [hcoeinv] at hjinv; exact hjinv
  have hj'inv0 : ((j'⁻¹ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))) : LaurentSeries L) ≠ 0 := by
    rw [hcoeinv, ne_eq, inv_eq_zero]; exact hj0
  have hconstN : ∀ y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))), IsAlgebraic L y → y ∈ (algebraMap L ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))).range :=
    fun y hy => mem_range_algebraMap_of_isAlgebraic _ (j⁻¹) hjinv0 hjinv hy
  have hconstM : ∀ y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))), IsAlgebraic L y → y ∈ (algebraMap L ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))).range :=
    fun y hy => mem_range_algebraMap_of_isAlgebraic _ (j'⁻¹) hj'inv0 hj'inv hy

  have hjΩ : ((ΦN j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [coe_liftHom, hj, coeffMap_coeffEmb']
  have hjΩmem : ((ΦN j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    rw [hjΩ]
    apply coeffEmb_mem_laurentBaseChange
    have h := jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 M')
    rw [jqModC_rat] at h
    exact intFormRatiosC_subset ℚ _ h
  have hFDL : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))))) ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hTH L (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) rfl j hj
  have hFDΩ : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({ΦN j} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hTH (AlgebraicClosure ℚ) (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) rfl (ΦN j) hjΩ
  have hιL : ιL.toRingHom.IsIntegral := isIntegral_inclusion L _ _ hle j hj'mem hFDL
  have hιΩ : ιΩ.toRingHom.IsIntegral := isIntegral_inclusion (AlgebraicClosure ℚ) _ _ hleΩ (ΦN j) hjΩmem hFDΩ
  have hιΩL : ιΩL.toRingHom.IsIntegral := hιΩ
  have hΦN : ΦN.toRingHom.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) x
  have hΦM : ΦM.toRingHom.IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))) x

  obtain ⟨W, hW⟩ := Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
    (K := L) (K' := AlgebraicClosure ℚ) (F := ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) (F' := ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) hgenN hconstN
    (M := ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) P
  have e1N : (W.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) = 1 :=
    Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgenN hconstN W
  let W' : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := W.restrictAlong ιΩ hιΩ
  have e1M : (W'.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) = 1 :=
    Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgenM hconstM W'

  have hordeq : ∀ f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))), W.ord (ΦN f) = P.ord f := by
    intro f
    have h := (W.forgetConstants (K := L)).ord_restrict (F := ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))))) f
    rw [hW, e1N, Place.ord_forgetConstants, RingHom.algebraMap_toAlgebra, Nat.cast_one, one_mul] at h
    rw [← liftHom_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
    exact h
  have hP0Ω : W.ord (ΦN j) = 0 := by rw [hordeq]; exact hP0
  have hP1728Ω : W.ord (ΦN j - 1728) = 0 := by
    have h := hordeq (j - 1728)
    rw [map_sub, map_ofNat] at h
    rw [h]; exact hP1728

  have eΩ : Place.ramificationIndexAlong ιΩ W = 1 :=
    coreBar q M' (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) rfl (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) rfl hleΩ (ΦN j) hjΩ W hP0Ω hP1728Ω

  have hc1 := Place.ramificationIndexAlong_comp ιL ΦN hιL hΦN
    (RingHom.IsIntegral.trans ιL.toRingHom ΦN.toRingHom hιL hΦN) (W.forgetConstants (K := L))
  have hc2 := Place.ramificationIndexAlong_comp ΦM ιΩL hΦM hιΩL
    (RingHom.IsIntegral.trans ΦM.toRingHom ιΩL.toRingHom hΦM hιΩL) (W.forgetConstants (K := L))
  have d1 : Place.ramificationIndexAlong ΦN (W.forgetConstants (K := L)) =
      (W.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))) := rfl
  have d2 : (W.forgetConstants (K := L)).restrictAlong ΦN hΦN = P := by rw [← hW]; rfl
  have d3 : Place.ramificationIndexAlong ιΩL (W.forgetConstants (K := L)) = Place.ramificationIndexAlong ιΩ W :=
    ramificationIndexAlong_restrictScalars_forgetConstants ιΩ W
  have d4 : (W.forgetConstants (K := L)).restrictAlong ιΩL hιΩL = W'.forgetConstants (K := L) :=
    restrictAlong_restrictScalars_forgetConstants ιΩ hιΩ W
  have d5 : Place.ramificationIndexAlong ΦM (W'.forgetConstants (K := L)) =
      (W'.forgetConstants (K := L)).ramificationIndex ↥(ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) := rfl
  rw [hsq] at hc1
  rw [hc1, d1, e1N, d2, d3, eΩ, d4, d5, e1M, one_mul, mul_one] at hc2
  exact hc2

end
end S_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH_of_eq_two (solution)
