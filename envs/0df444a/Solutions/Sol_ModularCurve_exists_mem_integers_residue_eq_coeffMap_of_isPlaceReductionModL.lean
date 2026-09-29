-- Prove2me | solution 1 for ModularCurve.exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1a606889-cfe4-56c8-9c19-c4e050ba0977

import Theorems.Thm_ModularCurve_coeffMap_residue_mem_modularFunctionFieldFullC_of_not_dvd
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve IsLocalRing

noncomputable section

namespace QExpPrincipleSol

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem min_ord_le_ord_add (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  set m := min (v.ord f) (v.ord g) with hm
  have h1 : v.adicValuation f ≤ WithZero.exp (-m) := by
    rw [v.adicValuation_le_exp_iff, neg_neg]; exact Or.inr (min_le_left _ _)
  have h2 : v.adicValuation g ≤ WithZero.exp (-m) := by
    rw [v.adicValuation_le_exp_iff, neg_neg]; exact Or.inr (min_le_right _ _)
  have h := (v.adicValuation.map_add f g).trans (max_le h1 h2)
  rw [v.adicValuation_le_exp_iff, neg_neg] at h
  exact h.resolve_left hfg

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem ord_smul (v : Place K F) {c : K} (hc : c ≠ 0) (f : F) : v.ord (c • f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap, zero_add]

theorem forall_ord_eq_zero_of_forall_ord_le_zero [HasPrincipalDivisors K F]
    (hdeg : ∀ v : Place K F, 0 < v.deg) {w : F} (hw : w ≠ 0) (h : ∀ v : Place K F, v.ord w ≤ 0) :
    ∀ v : Place K F, v.ord w = 0 := by
  classical
  obtain ⟨D, hD, hdeg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) w hw
  have hterm : ∀ v ∈ D.support, (fun v n => n * (v.deg : ℤ)) v (D v) ≤ 0 := by
    intro v _
    have : D v ≤ 0 := by rw [hD v]; exact h v
    exact mul_nonpos_of_nonpos_of_nonneg this (Int.natCast_nonneg _)
  have hsum : Divisor.degree D = D.sum fun v n => n * (v.deg : ℤ) := by
    simp [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rw [hsum, Finsupp.sum] at hdeg0
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hdeg0
  intro v
  by_contra hv
  have hvs : v ∈ D.support := by
    rw [Finsupp.mem_support_iff, hD v]; exact hv
  have h0 := hall v hvs
  simp only at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · rw [hD v] at h1; exact hv h1
  · exact absurd h1 (by exact_mod_cast (hdeg v).ne')

end Generic

section Fibre

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable (k : Type*) [Field k] [IsAlgClosed k] {p : ℕ} [Fact p.Prime] [CharP k p]
  (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)

abbrev jFb : modularFunctionFieldFullC k N := ⟨jqModC k, jqModC_mem_full k N⟩

theorem transcendental_jFb : Transcendental k (jFb k N) := by
  intro halg
  apply ModularCurve.transcendental_jqModC k
  exact halg.algHom (modularFunctionFieldFullC k N).val

include hpN in
theorem natCast_level_ne_zero : (N : k) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff k p] at h
  exact hpN h

theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    rw [Finset.mem_filter]
    exact ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have := Finset.single_le_sum (f := fun d => N / d) (fun d _ => Nat.zero_le _) h1
  simp only [Nat.div_one] at this
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) this

include hpN in
theorem finiteDimensional_adjoin_jFb :
    FiniteDimensional (IntermediateField.adjoin k ({jFb k N} : Set (modularFunctionFieldFullC k N)))
      (modularFunctionFieldFullC k N) := by
  have h := ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi k N
    (natCast_level_ne_zero k N hpN)
  exact Module.finite_of_finrank_pos (by rw [h]; exact dedekindPsi_pos N)

theorem hasPrincipalDivisors_Fb : HasPrincipalDivisors k (modularFunctionFieldFullC k N) :=
  (ModularCurve.isCurveOver_modularFunctionFieldFullC k N).toHasPrincipalDivisors

theorem deg_pos_Fb (v : Place k (modularFunctionFieldFullC k N)) : 0 < v.deg := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC k N
  haveI : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
  exact Module.finrank_pos

include hpN in

theorem exists_eq_algebraMap_of_forall_ord_eq_zero {w : modularFunctionFieldFullC k N}
    (h : ∀ v : Place k (modularFunctionFieldFullC k N), v.ord w = 0) :
    ∃ c : k, w = algebraMap k _ c := by
  haveI := finiteDimensional_adjoin_jFb k N hpN
  obtain ⟨c, hc⟩ := AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
    (jFb k N) (transcendental_jFb k N) h
  exact ⟨c, hc.symm⟩

include hpN in

theorem exists_ord_pos {w : modularFunctionFieldFullC k N} (hw : w ≠ 0)
    (hnc : ∀ c : k, w ≠ algebraMap k _ c) :
    ∃ v : Place k (modularFunctionFieldFullC k N), 0 < v.ord w := by
  by_contra hno
  push Not at hno
  haveI := hasPrincipalDivisors_Fb k N
  have h0 := forall_ord_eq_zero_of_forall_ord_le_zero (deg_pos_Fb k N) hw hno
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_forall_ord_eq_zero k N hpN h0
  exact hnc c hc

include hpN in

theorem eq_of_forall_ord_sub_eq {φ ψ : modularFunctionFieldFullC k N}
    (hψ : ∀ c : k, ψ ≠ algebraMap k _ c)
    (h : ∀ (a : k) (v : Place k (modularFunctionFieldFullC k N)),
      v.ord (φ - algebraMap k _ a) = v.ord (ψ - algebraMap k _ a)) : φ = ψ := by
  classical

  obtain ⟨a₁, a₂, hne, ha₁, ha₂⟩ : ∃ a₁ a₂ : k, a₁ ≠ a₂ ∧ φ - algebraMap k _ a₁ ≠ 0 ∧
      φ - algebraMap k _ a₂ ≠ 0 := by
    by_cases hφ : ∃ c : k, φ = algebraMap k _ c
    · obtain ⟨c, hc⟩ := hφ
      obtain ⟨a₁, ha₁⟩ := Infinite.exists_notMem_finset ({c} : Finset k)
      obtain ⟨a₂, ha₂⟩ := Infinite.exists_notMem_finset ({c, a₁} : Finset k)
      simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha₁ ha₂
      refine ⟨a₁, a₂, Ne.symm ha₂.2, ?_, ?_⟩
      · rw [hc, ← map_sub, map_ne_zero_iff _ (algebraMap k _).injective, sub_ne_zero]
        exact Ne.symm ha₁
      · rw [hc, ← map_sub, map_ne_zero_iff _ (algebraMap k _).injective, sub_ne_zero]
        exact Ne.symm ha₂.1
    · push Not at hφ
      refine ⟨0, 1, zero_ne_one, ?_, ?_⟩ <;> exact sub_ne_zero.mpr (hφ _)

  have hconst : ∀ a : k, φ - algebraMap k _ a ≠ 0 →
      ∃ κ : k, φ - algebraMap k _ a = κ • (ψ - algebraMap k _ a) := by
    intro a ha
    have hψa : ψ - algebraMap k _ a ≠ 0 := sub_ne_zero.mpr (hψ a)
    set z := (φ - algebraMap k _ a) * (ψ - algebraMap k _ a)⁻¹ with hz
    have hz0 : ∀ v : Place k (modularFunctionFieldFullC k N), v.ord z = 0 := by
      intro v
      rw [hz, v.ord_mul ha (inv_ne_zero hψa), v.ord_inv, h a v]; ring
    obtain ⟨κ, hκ⟩ := exists_eq_algebraMap_of_forall_ord_eq_zero k N hpN hz0
    refine ⟨κ, ?_⟩
    rw [Algebra.smul_def, ← hκ, hz, mul_assoc, inv_mul_cancel₀ hψa, mul_one]
  obtain ⟨κ₁, h₁⟩ := hconst a₁ ha₁
  obtain ⟨κ₂, h₂⟩ := hconst a₂ ha₂

  have hdiff : (κ₁ - κ₂) • ψ = algebraMap k _ (a₂ - a₁ + κ₁ * a₁ - κ₂ * a₂) := by
    have e : (φ - algebraMap k _ a₁) - (φ - algebraMap k _ a₂)
        = κ₁ • (ψ - algebraMap k _ a₁) - κ₂ • (ψ - algebraMap k _ a₂) := by rw [h₁, h₂]
    simp only [map_add, map_sub, map_mul, Algebra.smul_def] at e ⊢
    linear_combination -e
  have hκ : κ₁ = κ₂ := by
    by_contra hκne
    have hne0 : κ₁ - κ₂ ≠ 0 := sub_ne_zero.mpr hκne
    apply hψ ((κ₁ - κ₂)⁻¹ * (a₂ - a₁ + κ₁ * a₁ - κ₂ * a₂))
    rw [map_mul, ← hdiff, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne0, map_one,
      one_mul]
  subst hκ
  rw [sub_self, zero_smul] at hdiff
  have h0 : a₂ - a₁ + κ₁ * a₁ - κ₁ * a₂ = 0 :=
    (map_eq_zero_iff _ (algebraMap k (modularFunctionFieldFullC k N)).injective).mp hdiff.symm
  have hκ1 : κ₁ = 1 := by
    have : (a₂ - a₁) * (1 - κ₁) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) (Ne.symm hne)
    · linear_combination -h
  rw [hκ1, one_smul] at h₁
  linear_combination h₁

end Fibre

section Reduction

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

theorem residue_algebraMap_eq_zero_of_mem_nonunits {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] (R : ConstantReduction A F Fbar)
    {x : L} (hx : x ∈ A.nonunits) :
    ∃ hm : algebraMap L F x ∈ R.integers, R.residue ⟨algebraMap L F x, hm⟩ = 0 := by
  have hxA : x ∈ A := A.nonunits_subset hx
  have hm : algebraMap L F x ∈ R.integers := (R.algebraMap_mem_iff x).mpr hxA
  refine ⟨hm, ?_⟩
  rw [← RingHom.mem_ker, R.ker_residue, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := IsUnit.exists_right_inv hu
  have hvF : algebraMap L F x * (v : F) = 1 := by
    have := congrArg Subtype.val hv; simpa using this
  have hx0 : algebraMap L F x ≠ 0 := left_ne_zero_of_mul_eq_one hvF
  have hvinv : (v : F) = (algebraMap L F x)⁻¹ := eq_inv_of_mul_eq_one_right hvF
  have hinvmem : algebraMap L F x⁻¹ ∈ R.integers := by rw [map_inv₀, ← hvinv]; exact v.2
  have hxinvA : x⁻¹ ∈ A := (R.algebraMap_mem_iff _).mp hinvmem
  rw [ValuationSubring.mem_nonunits_iff] at hx
  have h1 : A.valuation x⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hxinvA
  have hx0' : x ≠ 0 := by rintro rfl; simp at hx0
  have h2 : A.valuation (x * x⁻¹) < 1 := by rw [map_mul]; exact mul_lt_one_of_lt_of_le hx h1
  rw [mul_inv_cancel₀ hx0', map_one] at h2
  exact lt_irrefl _ h2

variable (N : ℕ) [NeZero N] {p : ℕ} [Fact p.Prime] (hpN : ¬ p ∣ N)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  (R : ConstantReduction A (modularFunctionFieldBar N)
    (modularFunctionFieldFullC (ResidueField A) N))
  (hR : IsPlaceReductionModL A N R.placeMap)

def gA (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) :
    modularFunctionFieldBar N := ⟨coeffMap A.subtype y, hy⟩

def redF (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) :
    modularFunctionFieldFullC (ResidueField A) N :=
  ⟨coeffMap (residue A) y,
    ModularCurve.coeffMap_residue_mem_modularFunctionFieldFullC_of_not_dvd N hpN A hA y hy⟩

variable {N A}

theorem gA_ne_zero {y : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hne : coeffMap (residue A) y ≠ 0) : gA N A y hy ≠ 0 := by
  intro h0
  apply hne
  have h1 : coeffMap A.subtype y = 0 := congrArg Subtype.val h0
  have hy0 : y = 0 := by
    ext n
    have h2 := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => HahnSeries.coeff z n) h1
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h2
    have h3 : y.coeff n = 0 := Subtype.ext h2
    rw [h3]; rfl
  rw [hy0, map_zero]

theorem mem_sub_C {y : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) (a : A) :
    coeffMap A.subtype (y - HahnSeries.C a) ∈ modularFunctionFieldBar N := by
  rw [map_sub, HahnSeries.C_apply, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
  exact sub_mem hy ((modularFunctionFieldBar N).algebraMap_mem _)

theorem gA_sub_C {y : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) (a : A) :
    gA N A (y - HahnSeries.C a) (mem_sub_C hy a)
      = gA N A y hy - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) := by
  apply Subtype.ext
  simp only [gA, map_sub, HahnSeries.C_apply, coeffMap_single]
  rw [← algebraMap_laurentSeries_eq_single]
  rfl

theorem mem_add {y y' : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hy' : coeffMap A.subtype y' ∈ modularFunctionFieldBar N) :
    coeffMap A.subtype (y + y') ∈ modularFunctionFieldBar N := by
  rw [map_add]; exact add_mem hy hy'

theorem gA_add {y y' : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hy' : coeffMap A.subtype y' ∈ modularFunctionFieldBar N) :
    gA N A (y + y') (mem_add hy hy') = gA N A y hy + gA N A y' hy' :=
  Subtype.ext (by simp only [gA, map_add]; rfl)

include hpN hA in
theorem redF_sub_C {y : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) (a : A) :
    redF N hpN A hA (y - HahnSeries.C a) (mem_sub_C hy a)
      = redF N hpN A hA y hy - algebraMap (ResidueField A) _ (residue A a) := by
  apply Subtype.ext
  simp only [redF, map_sub, HahnSeries.C_apply, coeffMap_single]
  rw [← algebraMap_laurentSeries_eq_single]
  rfl

include hpN hA in
theorem redF_add {y y' : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hy' : coeffMap A.subtype y' ∈ modularFunctionFieldBar N) :
    redF N hpN A hA (y + y') (mem_add hy hy') = redF N hpN A hA y hy + redF N hpN A hA y' hy' :=
  Subtype.ext (by simp only [redF, map_add]; rfl)

include hR in

theorem ord_residue_eq {y : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hne : coeffMap (residue A) y ≠ 0) (u : R.integers) (hu : R.residue u ≠ 0)
    (hord : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      P.ord (u : modularFunctionFieldBar N) = P.ord (gA N A y hy)) :
    ∀ Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N),
      Q.ord (R.residue u) = Q.ord (redF N hpN A hA y hy) := by
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    (gA N A y hy) (gA_ne_zero hy hne)
  intro Q
  have h1 := R.mapDomain_placeMap u hu D (fun P => by rw [hD P, hord P]) Q
  have h2 := hR.2 y hy (redF N hpN A hA y hy).2 hne D hD Q
  exact h1.symm.trans h2

include hR in

theorem unit_of_nonconstant [IsAlgClosed (ResidueField A)] [CharP (ResidueField A) p]
    {y : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hnc : ∀ κ : ResidueField A, redF N hpN A hA y hy ≠ algebraMap (ResidueField A) _ κ) :
    ∃ h : gA N A y hy ∈ R.integers, R.residue ⟨gA N A y hy, h⟩ ≠ 0 ∧
      ∀ Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N),
        Q.ord (R.residue ⟨gA N A y hy, h⟩) = Q.ord (redF N hpN A hA y hy) := by
  set k := ResidueField A
  have hne : coeffMap (residue A) y ≠ 0 := by
    intro h0; apply hnc 0
    apply Subtype.ext
    simp only [redF, h0, map_zero, ZeroMemClass.coe_zero]
  have hg0 : gA N A y hy ≠ 0 := gA_ne_zero hy hne
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem (gA N A y hy) hg0
  have hc0 : c ≠ 0 := by
    rintro rfl; apply hres
    have : (⟨(0 : AlgebraicClosure ℚ) • gA N A y hy, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]

  have hne_a : ∀ a : A, coeffMap (residue A) (y - HahnSeries.C a) ≠ 0 := by
    intro a h0
    apply hnc (residue A a)
    have h1 := redF_sub_C hpN hA hy a
    have h2 : redF N hpN A hA (y - HahnSeries.C a) (mem_sub_C hy a) = 0 := Subtype.ext h0
    rw [h2] at h1
    exact sub_eq_zero.mp h1.symm

  have hg_eq : gA N A y hy = algebraMap _ _ c⁻¹ * (c • gA N A y hy) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  by_cases hcA : c ∈ A
  · by_cases hcn : c ∈ A.nonunits
    ·
      exfalso
      have hE : ∀ (a : A) (Q : Place k (modularFunctionFieldFullC k N)),
          Q.ord (R.residue ⟨c • gA N A y hy, hc⟩)
            = Q.ord (redF N hpN A hA y hy - algebraMap k _ (residue A a)) := by
        intro a
        have hca : (c * a : AlgebraicClosure ℚ) ∈ A.nonunits := by
          rw [ValuationSubring.mem_nonunits_iff] at hcn ⊢
          rw [map_mul]
          exact mul_lt_one_of_lt_of_le hcn (A.valuation_le_one a)
        obtain ⟨hm, hres0⟩ := residue_algebraMap_eq_zero_of_mem_nonunits R hca
        have hmem_a : c • gA N A (y - HahnSeries.C a) (mem_sub_C hy a) ∈ R.integers := by
          rw [gA_sub_C hy a, smul_sub, Algebra.smul_def c (algebraMap _ _ (a : AlgebraicClosure ℚ)),
            ← map_mul]
          exact sub_mem hc hm
        have hres_a : R.residue ⟨_, hmem_a⟩ = R.residue ⟨c • gA N A y hy, hc⟩ := by
          have : (⟨_, hmem_a⟩ : R.integers) = ⟨c • gA N A y hy, hc⟩ - ⟨_, hm⟩ := by
            apply Subtype.ext
            show c • gA N A (y - HahnSeries.C a) (mem_sub_C hy a)
              = c • gA N A y hy - algebraMap _ _ (c * a)
            rw [gA_sub_C hy a, smul_sub, Algebra.smul_def c (algebraMap _ _ (a : AlgebraicClosure ℚ)),
              ← map_mul]
          rw [this, map_sub, hres0, sub_zero]
        have hu_a : R.residue ⟨_, hmem_a⟩ ≠ 0 := by rw [hres_a]; exact hres
        have hord_a := ord_residue_eq hpN hA R hR (mem_sub_C hy a) (hne_a a) ⟨_, hmem_a⟩ hu_a
          (fun P => ord_smul P hc0 _)
        intro Q
        rw [← hres_a, hord_a Q, redF_sub_C hpN hA hy a]

      set ψ := redF N hpN A hA y hy with hψ
      have hψ0 : ψ ≠ 0 := fun h0 => hnc 0 (by rw [h0, map_zero])
      obtain ⟨Q₀, hQ₀⟩ := exists_ord_pos k N hpN hψ0 hnc
      have hE0 := hE 0 Q₀
      have hE1 := hE 1 Q₀
      simp only [map_zero, sub_zero] at hE0
      simp only [map_one] at hE1
      have hpos1 : 0 < Q₀.ord (ψ - 1) := by rw [← hE1, hE0]; exact hQ₀
      have hψ1 : ψ - 1 ≠ 0 := fun h0 => hnc 1 (by rw [map_one]; exact sub_eq_zero.mp h0)
      have hneg : Q₀.ord (-(ψ - 1)) = Q₀.ord (ψ - 1) := by
        rw [← neg_one_smul k (ψ - 1), ord_smul Q₀ (by norm_num) (ψ - 1)]
      have hsum : ψ + -(ψ - 1) = 1 := by ring
      have hmin := min_ord_le_ord_add Q₀ hψ0 (neg_ne_zero.mpr hψ1) (by rw [hsum]; exact one_ne_zero)
      rw [hsum, Place.ord_one, hneg] at hmin
      exact absurd hmin (not_le.mpr (lt_min hQ₀ hpos1))
    ·
      have hval1 : A.valuation c = 1 := by
        rcases A.valuation_lt_one_or_eq_one ⟨c, hcA⟩ with h | h
        · exact absurd (A.mem_nonunits_iff.mpr h) hcn
        · exact h
      have hcinvA : c⁻¹ ∈ A := by rw [← A.valuation_le_one_iff, map_inv₀, hval1, inv_one]
      have hcinv_mem : algebraMap _ (modularFunctionFieldBar N) c⁻¹ ∈ R.integers :=
        (R.algebraMap_mem_iff _).mpr hcinvA
      have hgmem : gA N A y hy ∈ R.integers := by rw [hg_eq]; exact mul_mem hcinv_mem hc
      have hres_g : R.residue ⟨gA N A y hy, hgmem⟩
          = algebraMap k _ (residue A ⟨c⁻¹, hcinvA⟩) * R.residue ⟨c • gA N A y hy, hc⟩ := by
        have : (⟨gA N A y hy, hgmem⟩ : R.integers) = ⟨_, hcinv_mem⟩ * ⟨c • gA N A y hy, hc⟩ :=
          Subtype.ext hg_eq
        rw [this, map_mul, ← R.residue_algebraMap ⟨c⁻¹, hcinvA⟩]
      have hunit_res : residue A ⟨c⁻¹, hcinvA⟩ ≠ 0 := by
        rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          not_not, A.valuation_eq_one_iff]
        show A.valuation c⁻¹ = 1
        rw [map_inv₀, hval1, inv_one]
      have hres_ne : R.residue ⟨gA N A y hy, hgmem⟩ ≠ 0 := by
        rw [hres_g]; exact mul_ne_zero ((map_ne_zero _).mpr hunit_res) hres
      exact ⟨hgmem, hres_ne, ord_residue_eq hpN hA R hR hy hne ⟨_, hgmem⟩ hres_ne (fun P => rfl)⟩
  ·
    exfalso
    have hcinvA : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    have hcinv_nu : c⁻¹ ∈ A.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff, map_inv₀]
      have hpos : 0 < A.valuation c := zero_lt_iff.mpr ((map_ne_zero A.valuation).mpr hc0)
      rw [inv_lt_one₀ hpos]
      exact lt_of_not_ge fun h => hcA ((A.valuation_le_one_iff c).mp h)
    obtain ⟨hm, hres0⟩ := residue_algebraMap_eq_zero_of_mem_nonunits R hcinv_nu
    have hgmem : gA N A y hy ∈ R.integers := by rw [hg_eq]; exact mul_mem hm hc
    have hres_g : R.residue ⟨gA N A y hy, hgmem⟩ = 0 := by
      have : (⟨gA N A y hy, hgmem⟩ : R.integers) = ⟨_, hm⟩ * ⟨c • gA N A y hy, hc⟩ :=
        Subtype.ext hg_eq
      rw [this, map_mul, hres0, zero_mul]

    have hy1 := mem_sub_C hy 1
    have hg1 : gA N A (y - HahnSeries.C 1) hy1 = gA N A y hy - 1 := by
      rw [gA_sub_C hy 1]; simp
    have hmem1 : gA N A (y - HahnSeries.C 1) hy1 ∈ R.integers := by
      rw [hg1]; exact sub_mem hgmem (one_mem _)
    have hres1 : R.residue ⟨_, hmem1⟩ = -1 := by
      have : (⟨_, hmem1⟩ : R.integers) = ⟨gA N A y hy, hgmem⟩ - 1 := Subtype.ext hg1
      rw [this, map_sub, map_one, hres_g, zero_sub]
    have hu1 : R.residue ⟨_, hmem1⟩ ≠ 0 := by rw [hres1]; exact neg_ne_zero.mpr one_ne_zero
    have hord1 := ord_residue_eq hpN hA R hR hy1 (hne_a 1) ⟨_, hmem1⟩ hu1 (fun P => rfl)
    have h0 : ∀ Q : Place k (modularFunctionFieldFullC k N),
        Q.ord (redF N hpN A hA (y - HahnSeries.C 1) hy1) = 0 := by
      intro Q
      rw [← hord1 Q, hres1, ← neg_one_smul k (1 : modularFunctionFieldFullC k N),
        ord_smul Q (by norm_num), Place.ord_one]
    obtain ⟨κ, hκ⟩ := exists_eq_algebraMap_of_forall_ord_eq_zero k N hpN h0
    apply hnc (κ + 1)
    rw [redF_sub_C hpN hA hy 1, map_one, sub_eq_iff_eq_add] at hκ
    rw [hκ, map_add, map_one]

include hR in

theorem residue_eq_of_nonconstant [IsAlgClosed (ResidueField A)] [CharP (ResidueField A) p]
    {y : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hnc : ∀ κ : ResidueField A, redF N hpN A hA y hy ≠ algebraMap (ResidueField A) _ κ) :
    ∃ h : gA N A y hy ∈ R.integers, R.residue ⟨gA N A y hy, h⟩ = redF N hpN A hA y hy := by
  set k := ResidueField A
  obtain ⟨h, hres0, hord⟩ := unit_of_nonconstant hpN hA R hR hy hnc
  refine ⟨h, ?_⟩
  apply eq_of_forall_ord_sub_eq k N hpN hnc
  intro abar Q
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective abar
  have hnc_a : ∀ κ : k, redF N hpN A hA (y - HahnSeries.C a) (mem_sub_C hy a) ≠ algebraMap k _ κ := by
    intro κ hκ
    apply hnc (κ + residue A a)
    rw [redF_sub_C hpN hA hy a, sub_eq_iff_eq_add] at hκ
    rw [hκ, map_add]
  obtain ⟨h_a, -, hord_a⟩ := unit_of_nonconstant hpN hA R hR (mem_sub_C hy a) hnc_a
  have hm : algebraMap _ (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) ∈ R.integers :=
    (R.algebraMap_mem_iff _).mpr a.2
  have hres_a : R.residue ⟨gA N A (y - HahnSeries.C a) (mem_sub_C hy a), h_a⟩
      = R.residue ⟨gA N A y hy, h⟩ - algebraMap k _ (residue A a) := by
    have : (⟨gA N A (y - HahnSeries.C a) (mem_sub_C hy a), h_a⟩ : R.integers)
        = ⟨gA N A y hy, h⟩ - ⟨_, hm⟩ := Subtype.ext (gA_sub_C hy a)
    rw [this, map_sub, ← R.residue_algebraMap a]
  rw [← hres_a, hord_a Q, redF_sub_C hpN hA hy a]

include hpN hA hR in

theorem main (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) :
    ∃ hmem : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
      ((R.residue ⟨_, hmem⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        coeffMap (IsLocalRing.residue A) y := by
  haveI : IsAlgClosed (ResidueField A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP (ResidueField A) p :=
    ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  set k := ResidueField A

  have hyJ : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar N := by
    rw [coeffMap_jqModC]
    have : jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq := by
      rw [coeffEmb, ← jqModC_rat, coeffMap_jqModC]
    rw [this]
    exact coeffEmb_mem_laurentBaseChange _ (modularFunctionField_le_full N (jq_mem N))
  have hJnc : ∀ κ : k, redF N hpN A hA (jqModC A) hyJ ≠ algebraMap k _ κ := by
    intro κ hκ
    have h1 := congrArg (fun z : modularFunctionFieldFullC k N => (z : LaurentSeries k).coeff (-1)) hκ
    simp only [redF, coeffMap_jqModC] at h1
    have h2 : ((algebraMap k (modularFunctionFieldFullC k N) κ : modularFunctionFieldFullC k N) :
        LaurentSeries k) = algebraMap k (LaurentSeries k) κ := rfl
    rw [ModularCurve.coeff_jqModC_neg_one, h2, algebraMap_laurentSeries_eq_single,
      HahnSeries.coeff_single_of_ne (by norm_num)] at h1
    exact one_ne_zero h1

  have hy' : coeffMap A.subtype (y + jqModC A) ∈ modularFunctionFieldBar N := mem_add hy hyJ
  by_cases hc : ∃ κ : k, redF N hpN A hA (y + jqModC A) hy' = algebraMap k _ κ
  · obtain ⟨κ, hκ⟩ := hc
    have hnc : ∀ κ' : k, redF N hpN A hA y hy ≠ algebraMap k _ κ' := by
      intro κ' hκ'
      apply hJnc (κ - κ')
      rw [redF_add hpN hA hy hyJ, hκ'] at hκ
      rw [map_sub, ← hκ]; ring
    obtain ⟨h, hres⟩ := residue_eq_of_nonconstant hpN hA R hR hy hnc
    exact ⟨h, congrArg Subtype.val hres⟩
  · push Not at hc
    obtain ⟨h', hres'⟩ := residue_eq_of_nonconstant hpN hA R hR hy' hc
    obtain ⟨hJ, hresJ⟩ := residue_eq_of_nonconstant hpN hA R hR hyJ hJnc
    have hg : gA N A y hy = gA N A (y + jqModC A) hy' - gA N A (jqModC A) hyJ := by
      rw [gA_add hy hyJ, add_sub_cancel_right]
    have hmem : gA N A y hy ∈ R.integers := by rw [hg]; exact sub_mem h' hJ
    refine ⟨hmem, ?_⟩
    have hsub : (⟨gA N A y hy, hmem⟩ : R.integers) = ⟨_, h'⟩ - ⟨_, hJ⟩ := Subtype.ext hg
    show ((R.residue ⟨gA N A y hy, hmem⟩ : modularFunctionFieldFullC k N) : LaurentSeries k) = _
    rw [hsub, map_sub, hres', hresJ, AddSubgroupClass.coe_sub]
    simp only [redF, map_add, add_sub_cancel_right]

end Reduction

end QExpPrincipleSol

end

open AlgebraicCurve ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] {p : ℕ} [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (R : ConstantReduction A (modularFunctionFieldBar N)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hR : IsPlaceReductionModL A N R.placeMap)
    (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) :
    ∃ hmem : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
      ((R.residue ⟨_, hmem⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        coeffMap (IsLocalRing.residue A) y :=
  QExpPrincipleSol.main hpN hA R hR y hy

end S_ModularCurve_exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL
end P2MW
export P2MW.S_ModularCurve_exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL (solution)
