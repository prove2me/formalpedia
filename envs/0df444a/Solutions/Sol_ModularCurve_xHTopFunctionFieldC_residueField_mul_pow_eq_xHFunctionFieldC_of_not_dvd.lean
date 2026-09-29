-- Prove2me | solution 1 for ModularCurve.xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d7f19c07-18ac-542a-a1ca-dea25e22405f

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical MatrixGroups
p2m_open "IntermediateField AlgebraicCurve ModularCurve~order_qExpand CongruenceSubgroup"

namespace XHTopResidueCollapsePow

section Groups

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (t : ℕ)

abbrev Gam : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H

abbrev Gam' : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H ⊓ Gamma0 (M * t)

abbrev Hpm : Subgroup (ZMod M)ˣ := H ⊔ Subgroup.zpowers (-1)

omit [NeZero M] in
theorem Gam'_le : Gam' M H t ≤ Gam M H := inf_le_left

scoped instance : (Gam M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance [NeZero t] : (Gam' M H t).FiniteIndex := by
  haveI : NeZero (M * t) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * t)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M t)).trans (Gamma1_le_GammaH M H)

scoped instance [NeZero t] : (CohCarrier.GammaH M (Hpm M H) ⊓ Gamma0 t).FiniteIndex := by
  haveI : NeZero (M * t) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * t)) (le_inf ?_ ?_)
  · exact (Gamma1_le_of_dvd (dvd_mul_right M t)).trans (Gamma1_le_GammaH M _)
  · exact (Gamma1_le_of_dvd (dvd_mul_left t M)).trans (Gamma1_in_Gamma0 _)

omit [NeZero M] in
theorem T_mem_Gam' : ModularGroup.T ∈ Gam' M H t := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

omit [NeZero M] in

theorem Gam'_le_pm : Gam' M H t ≤ CohCarrier.GammaH M (Hpm M H) ⊓ Gamma0 (M * t) :=
  inf_le_inf_right _ (GammaH_mono le_sup_left)

omit [NeZero M] in

theorem neg_mem_Gamma0 {n : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 n) : -γ ∈ Gamma0 n := by
  rw [Gamma0_mem] at h ⊢
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, h, neg_zero]

omit [NeZero M] in

theorem gamma0Units_neg {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 M) :
    CohCarrier.gamma0Units M ⟨-γ, neg_mem_Gamma0 h⟩ = -CohCarrier.gamma0Units M ⟨γ, h⟩ := by
  ext
  rw [Units.val_neg, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  change (((-γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = -(((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]

omit [NeZero M] in

theorem eq_one_or_eq_neg_one_of_mem_zpowers {z : (ZMod M)ˣ} (hz : z ∈ Subgroup.zpowers (-1)) :
    z = 1 ∨ z = -1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rcases Int.even_or_odd k with hk | hk
  · exact Or.inl hk.neg_one_zpow
  · exact Or.inr hk.neg_one_zpow

omit [NeZero M] in

theorem mem_or_neg_mem_of_mem_pm {γ : SL(2, ℤ)}
    (hγ : γ ∈ CohCarrier.GammaH M (Hpm M H) ⊓ Gamma0 (M * t)) :
    γ ∈ Gam' M H t ∨ -γ ∈ Gam' M H t := by
  obtain ⟨hγH, hγ0⟩ := Subgroup.mem_inf.mp hγ
  obtain ⟨hγM, hu⟩ := CohCarrier.mem_GammaH_iff.mp hγH
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hu
  rcases eq_one_or_eq_neg_one_of_mem_zpowers M hz with rfl | rfl
  · left
    rw [mul_one] at hyz
    refine Subgroup.mem_inf.mpr ⟨CohCarrier.mem_GammaH_iff.mpr ⟨hγM, ?_⟩, hγ0⟩
    rw [← hyz]; exact hy
  · right
    refine Subgroup.mem_inf.mpr ⟨CohCarrier.mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 hγM, ?_⟩,
      neg_mem_Gamma0 hγ0⟩
    rw [gamma0Units_neg M hγM, ← hyz, mul_neg_one, neg_neg]
    exact hy

omit [NeZero M] in

theorem pm_inf_Gamma0_le (htM : Nat.Coprime t M) :
    CohCarrier.GammaH M (Hpm M H) ⊓ Gamma0 t ≤ CohCarrier.GammaH M (Hpm M H) ⊓ Gamma0 (M * t) := by
  intro γ hγ
  obtain ⟨hγH, hγt⟩ := Subgroup.mem_inf.mp hγ
  refine Subgroup.mem_inf.mpr ⟨hγH, ?_⟩
  have hM : (M : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp (CohCarrier.GammaH_le_Gamma0 _ hγH))
  have ht : (t : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγt)
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hcop : IsCoprime (M : ℤ) (t : ℤ) := Nat.isCoprime_iff_coprime.mpr htM.symm
  have := hcop.mul_dvd hM ht
  push_cast
  exact this

theorem index_pm_le [NeZero t] (htM : Nat.Coprime t M) :
    (CohCarrier.GammaH M (Hpm M H) ⊓ Gamma0 (M * t)).index ≤
      (CohCarrier.GammaH M (Hpm M H)).index * (Gamma0 t).index :=
  (Subgroup.index_antitone (pm_inf_Gamma0_le M H t htM)).trans Subgroup.index_inf_le

end Groups

section Orders

variable (K : Type*) [Field K]

theorem coeff_order_ne_zero' {x : LaurentSeries K} (hx : x ≠ 0) : x.coeff x.order ≠ 0 :=
  fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)

theorem order_jqModC_pow (b : ℕ) : ((jqModC K) ^ b).order = -(b : ℤ) := by
  have h1 : ((jqModC K) ^ b).coeff (-(b : ℤ)) ≠ 0 := by
    rw [coeff_jqModC_pow_self]; exact one_ne_zero
  have hne : (jqModC K) ^ b ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push Not at hlt
  exact coeff_order_ne_zero' K hne (coeff_jqModC_pow_of_lt K hlt)

theorem jqModC_pow_ne_zero (b : ℕ) : (jqModC K) ^ b ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero (by rw [coeff_jqModC_pow_self]; exact one_ne_zero)

variable (p : ℕ) [NeZero p]

theorem order_qExpand {x : LaurentSeries K} (hx : x ≠ 0) :
    (qExpand K p x).order = (p : ℤ) * x.order := by
  have hq0 : qExpand K p x ≠ 0 := fun h => hx (qExpand_injective (R := K) (N := p) (by rw [h, map_zero]))
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [qExpand_coeff_mul]; exact coeff_order_ne_zero' K hx
  · by_contra hlt
    push Not at hlt
    have hc := coeff_order_ne_zero' K hq0
    by_cases hdvd : (p : ℤ) ∣ (qExpand K p x).order
    · obtain ⟨k, hk⟩ := hdvd
      rw [hk, qExpand_coeff_mul] at hc
      have hle := HahnSeries.order_le_of_coeff_ne_zero hc
      rw [hk] at hlt
      have hp : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
      nlinarith
    · exact hc (qExpand_coeff_of_not_dvd p x hdvd)

theorem eq_zero_of_sum_eq_zero_of_order_injOn {ι : Type*} [Fintype ι] (f : ι → LaurentSeries K)
    (hdist : ∀ i j, f i ≠ 0 → f j ≠ 0 → (f i).order = (f j).order → i = j)
    (hsum : ∑ i, f i = 0) : ∀ i, f i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  set s : Finset ι := Finset.univ.filter fun i => f i ≠ 0 with hs
  have hsne : s.Nonempty := ⟨i₁, by simp [hs, hi₁]⟩
  obtain ⟨i₀, hi₀s, hmin⟩ := Finset.exists_min_image s (fun i => (f i).order) hsne
  have hi₀ : f i₀ ≠ 0 := by simpa [hs] using hi₀s
  have hcoeff : (∑ i, f i).coeff (f i₀).order = (f i₀).coeff (f i₀).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ _) h)
    by_cases hti : f i = 0
    · rw [hti, HahnSeries.coeff_zero]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      have hle := hmin i (by simp [hs, hti])
      exact lt_of_le_of_ne hle fun h => hi (hdist i i₀ hti hi₀ h.symm)
  rw [hsum, HahnSeries.coeff_zero] at hcoeff
  exact coeff_order_ne_zero' K hi₀ hcoeff.symm

theorem pow_ne_jqModC (hp1 : 1 < p) (z : LaurentSeries K) : z ^ p ≠ jqModC K := by
  intro h
  by_cases hz : z = 0
  · rw [hz, zero_pow (NeZero.ne p)] at h
    exact jqModC_ne_zero_of_nontrivial K h.symm
  · have h1 : (z ^ p).order = ((jqModC K) ^ 1).order := by rw [h, pow_one]
    rw [HahnSeries.order_pow, order_jqModC_pow, nsmul_eq_mul] at h1
    push_cast at h1
    have h2 : (p : ℤ) ∣ 1 := ⟨-z.order, by linear_combination h1⟩
    have h3 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h2
    have h4 : (1 : ℤ) < p := by exact_mod_cast hp1
    linarith

theorem adjoin_pow_le :
    IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K))
      ≤ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
    (pow_mem (mem_adjoin_simple_self K (jqModC K)) p))

variable (hqj : qExpand K p (jqModC K) = (jqModC K) ^ p)
include hqj

theorem exists_qExpand_eq_of_mem_adjoin_pow {c : LaurentSeries K}
    (hc : c ∈ IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K))) :
    ∃ d : LaurentSeries K, qExpand K p d = c := by
  have hle : Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ {(jqModC K) ^ p})
      ≤ (qExpand K p).fieldRange := by
    rw [Subfield.closure_le]
    rintro z (⟨r, rfl⟩ | rfl)
    · refine ⟨algebraMap K (LaurentSeries K) r, ?_⟩
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
    · exact ⟨jqModC K, hqj⟩
  obtain ⟨d, hd⟩ := hle (show c ∈ Subfield.closure _ from hc)
  exact ⟨d, hd⟩

theorem le_finrank_adjoin_pow
    [Module.Finite (IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K)))
      (extendScalars (adjoin_pow_le K p))] :
    p ≤ Module.finrank (IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K)))
      (extendScalars (adjoin_pow_le K p)) := by
  set K₀ := IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K)) with hK₀
  let v : Fin p → extendScalars (adjoin_pow_le K p) := fun i =>
    ⟨(jqModC K) ^ (i : ℕ), (mem_extendScalars _).mpr
      (pow_mem (mem_adjoin_simple_self K (jqModC K)) _)⟩
  have hli : LinearIndependent K₀ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : ∑ i, ((g i : K₀) : LaurentSeries K) * (jqModC K) ^ (i : ℕ) = 0 := by
      have := congrArg (fun z : extendScalars (adjoin_pow_le K p) => (z : LaurentSeries K)) hg
      (first | exact this | simpa only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] using this | (have h__ := this; simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at h__; exact h__))
    have hd : ∀ i, ∃ d : LaurentSeries K, qExpand K p d = ((g i : K₀) : LaurentSeries K) :=
      fun i => exists_qExpand_eq_of_mem_adjoin_pow K p hqj (g i).2
    choose d hd using hd
    have hall := eq_zero_of_sum_eq_zero_of_order_injOn K
      (fun i : Fin p => ((g i : K₀) : LaurentSeries K) * (jqModC K) ^ (i : ℕ)) ?_ hsum
    · have hi := hall i
      rcases mul_eq_zero.mp hi with h0 | h0
      · exact Subtype.ext (by simpa using h0)
      · exact absurd h0 (jqModC_pow_ne_zero K _)
    · intro i j hi hj hij
      have hgi : ((g i : K₀) : LaurentSeries K) ≠ 0 := left_ne_zero_of_mul hi
      have hgj : ((g j : K₀) : LaurentSeries K) ≠ 0 := left_ne_zero_of_mul hj
      have hdi : d i ≠ 0 := by rintro h; apply hgi; rw [← hd i, h, map_zero]
      have hdj : d j ≠ 0 := by rintro h; apply hgj; rw [← hd j, h, map_zero]
      beta_reduce at hij
      rw [HahnSeries.order_mul hgi (jqModC_pow_ne_zero K _),
        HahnSeries.order_mul hgj (jqModC_pow_ne_zero K _), ← hd i, ← hd j,
        order_qExpand K p hdi, order_qExpand K p hdj, order_jqModC_pow, order_jqModC_pow] at hij
      have hdvd : (p : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) :=
        ⟨(d j).order - (d i).order, by linarith⟩
      have habs : |((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)| < p := by
        rw [abs_sub_lt_iff]; constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact Fin.ext (by omega)
  simpa using hli.fintype_card_le_finrank

omit hqj

scoped instance instNeZeroPrimePow (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

omit [NeZero p] in

theorem qExpand_prime_pow_jqModC (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (r : ℕ) :
    qExpand K (ℓ ^ r) (jqModC K) = (jqModC K) ^ (ℓ ^ r) := by
  haveI hℓ : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  induction r with
  | zero =>
      rw [qExpand_congr (pow_zero ℓ), qExpand_one_apply, pow_zero, pow_one]
  | succ r ih =>
      rw [qExpand_congr (pow_succ ℓ r), ← qExpand_qExpand (R := K) ℓ (ℓ ^ r),
        qExpand_jqModC_eq_pow_unconditional K, map_pow, ih, ← pow_mul, ← pow_succ]

end Orders

section Transport

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]

theorem mem_comap_iff (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) (x : F) :
    x ∈ R.integers.comap (w : F →+* F) ↔ w x ∈ R.integers := Iff.rfl

def comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    R.integers.comap (w : F →+* F) →+* R.integers :=
  (w : F →+* F).restrict _ _ (fun _ hx => (mem_comap_iff A R w _).mp hx)

@[scoped simp] theorem coe_comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers.comap (w : F →+* F)) : (comapHom A R w x : F) = w x := rfl

def symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    R.integers →+* R.integers.comap (w : F →+* F) :=
  (w.symm : F →+* F).restrict _ _ (fun x hx => by
    rw [mem_comap_iff]
    change w (w.symm x) ∈ R.integers
    rw [AlgEquiv.apply_symm_apply]; exact hx)

@[scoped simp] theorem coe_symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers) : (symmHom A R w x : F) = w.symm x := rfl

theorem comapHom_symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) (x : R.integers) :
    comapHom A R w (symmHom A R w x) = x :=
  Subtype.ext (by simp)

theorem symmHom_comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers.comap (w : F →+* F)) : symmHom A R w (comapHom A R w x) = x :=
  Subtype.ext (by simp)

def transport (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) : RegularProlongation A F Fb where
  integers := R.integers.comap (w : F →+* F)
  residue := R.residue.comp (comapHom A R w)
  algebraMap_mem_iff x := by
    rw [mem_comap_iff, AlgEquiv.commutes]
    exact R.algebraMap_mem_iff x
  residue_surjective z := by
    obtain ⟨f, hf⟩ := R.residue_surjective z
    exact ⟨symmHom A R w f, by rw [RingHom.comp_apply, comapHom_symmHom, hf]⟩
  ker_residue := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, R.ker_residue,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, not_iff_not]
    constructor
    · intro hu; simpa [symmHom_comapHom] using hu.map (symmHom A R w)
    · intro hu; exact hu.map (comapHom A R w)
  residue_algebraMap a := by
    rw [RingHom.comp_apply]
    convert R.residue_algebraMap a using 2
    exact Subtype.ext (by simp)
  exists_smul_mem f hf := by
    have hwf : w f ≠ 0 := (map_ne_zero_iff _ w.injective).mpr hf
    obtain ⟨c, hc, hne⟩ := R.exists_smul_mem (w f) hwf
    have hmem : c • f ∈ R.integers.comap (w : F →+* F) := by
      rw [mem_comap_iff, map_smul]; exact hc
    refine ⟨c, hmem, ?_⟩
    rw [RingHom.comp_apply]
    have h : comapHom A R w ⟨c • f, hmem⟩ = ⟨c • w f, hc⟩ := Subtype.ext (by simp)
    rwa [h]

@[scoped simp] theorem transport_integers (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    (transport A R w).integers = R.integers.comap (w : F →+* F) := rfl

theorem transport_residue_apply (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (f : F) (h₁ : f ∈ (transport A R w).integers) (h₀ : w f ∈ R.integers) :
    (transport A R w).residue ⟨f, h₁⟩ = R.residue ⟨w f, h₀⟩ := rfl

theorem ne_zero_of_residue_ne_zero (R : RegularProlongation A F Fb) {x : F} (hx : x ∈ R.integers)
    (hres : R.residue ⟨x, hx⟩ ≠ 0) : x ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨(0 : F), hx⟩ : R.integers) = 0 := Subtype.ext rfl
  rw [this, map_zero]

theorem inv_mem_of_residue_ne_zero (R : RegularProlongation A F Fb) {x : F} (hx : x ∈ R.integers)
    (hres : R.residue ⟨x, hx⟩ ≠ 0) : x⁻¹ ∈ R.integers := by
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hres
  have hmul : ((↑u⁻¹ : R.integers) : F) * x = 1 := by
    have := congrArg (fun y : R.integers => (y : F)) u.inv_mul
    simpa [hu] using this
  rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _

theorem residue_ne_zero_of_inv_mem (R : RegularProlongation A F Fb) {x : F} (hx0 : x ≠ 0)
    (hx : x ∈ R.integers) (hinv : x⁻¹ ∈ R.integers) : R.residue ⟨x, hx⟩ ≠ 0 := by
  have hunit : IsUnit (⟨x, hx⟩ : R.integers) :=
    ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩
  exact R.residue_ne_zero_of_isUnit hunit

end Transport

section Degrees

theorem relfinrank_adjoin_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (B : IntermediateField K E) (x : B) :
    relfinrank (adjoin K ({(x : E)} : Set E)) B = Module.finrank (adjoin K ({x} : Set B)) B := by
  have hc : (adjoin K ({(x : E)} : Set E)).comap B.val = adjoin K ({x} : Set B) := by
    apply le_antisymm
    · intro y hy
      change B.val y ∈ adjoin K ({(x : E)} : Set E) at hy
      have h' : (y : E) ∈ lift (adjoin K ({x} : Set B)) := by
        rw [lift_adjoin_simple]; exact hy
      exact (IntermediateField.mem_lift y).mp h'
    · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      change B.val x ∈ adjoin K ({(x : E)} : Set E)
      exact mem_adjoin_simple_self K (x : E)
  have h := IntermediateField.finrank_comap B.val (A := adjoin K ({(x : E)} : Set E))
  rw [fieldRange_val] at h
  rw [← h]
  exact congrArg (fun C : IntermediateField K B => Module.finrank C B) hc

end Degrees

section Constants

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem charP_residueField (q : ℕ) [Fact q.Prime] (A : ValuationSubring ℚ̄) (hA : A.LiesOverPrime q) :
    CharP (IsLocalRing.ResidueField A) q := by
  rw [CharP.charP_iff_prime_eq_zero Fact.out]
  have hq : ((q : A) : ℚ̄) ∈ A.nonunits := by (first | exact hA | simpa using hA | (have h__ := hA; simp at h__; exact h__))
  rw [ValuationSubring.coe_mem_nonunits_iff] at hq
  rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
  exact hq

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem laurentBaseChange_mono {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem jqModC_mem_laurentBaseChange (Γ : Subgroup SL(2, ℤ)) :
    jqModC L ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) := by
  have h : coeffEmb L (jqModC ℚ) = jqModC L := coeffMap_jqModC _
  rw [← h]
  exact coeffEmb_mem_laurentBaseChange L
    (intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ))

theorem jqModC_mem_qExpFunctionFieldC (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) :
    jqModC K ∈ qExpFunctionFieldC K Γ :=
  intFormRatiosC_subset K Γ (ModularCurve.jqModC_mem_intFormRatiosC K Γ)

end Constants

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (t : ℕ) [NeZero t]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "kk" => IsLocalRing.ResidueField A

local notation "EE" => laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * t))

local notation "Fb'" => xHTopFunctionFieldC (IsLocalRing.ResidueField A) M H (M * t)

local notation "Fb" => xHFunctionFieldC (IsLocalRing.ResidueField A) M H

omit [NeZero M] [NeZero t] in
theorem Fb_le_Fb' : (Fb) ≤ (Fb') := xHFunctionFieldC_le_top kk M H (M * t)

set_option maxHeartbeats 12800000 in

theorem main {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (hA : A.LiesOverPrime ℓ)
    (ht1 : 1 < t) (htM : Nat.Coprime t M)
    (hqj : qExpand kk t (jqModC kk) = (jqModC kk) ^ t)
    (hψ : (Gamma0 t).index < 2 * (t + 1)) : (Fb') = (Fb) := by

  obtain ⟨w, hw⟩ :=
    ModularCurve.exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime M H t htM
  obtain ⟨R₀, hR₀res⟩ : ∃ R₀ : RegularProlongation A EE Fb',
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ EE),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : EE) ∈ R₀.integers,
          ((R₀.residue ⟨_, hO⟩ : Fb') : LaurentSeries kk) = coeffMap (IsLocalRing.residue A) y := by
    obtain ⟨R₀, -, h⟩ :=
      ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC ℚ̄ A
        (Gam' M H t) (T_mem_Gam' M H t)
    exact ⟨R₀, h⟩
  let R₁ : RegularProlongation A EE Fb' := transport A R₀ w

  set f : EE := ⟨jqModC ℚ̄, jqModC_mem_laurentBaseChange ℚ̄ (Gam' M H t)⟩ with hfdef
  have hcoe_f : (f : LaurentSeries ℚ̄) = jqModC ℚ̄ := rfl
  have hfK : (f : LaurentSeries ℚ̄) ∈ xHFunctionFieldBar M H :=
    jqModC_mem_laurentBaseChange ℚ̄ (Gam M H)
  set g : EE := w f with hgdef
  have hcoe_g : (g : LaurentSeries ℚ̄) = qExpand ℚ̄ t (jqModC ℚ̄) := hw f hfK
  have hwf : w f = g := rfl

  have hι_j : coeffMap A.subtype (jqModC A) = jqModC ℚ̄ := coeffMap_jqModC _
  have hι_jq : coeffMap A.subtype (qExpand A t (jqModC A)) = qExpand ℚ̄ t (jqModC ℚ̄) := by
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC]
  have hfmem : coeffMap A.subtype (jqModC A) ∈ EE := by rw [hι_j, ← hcoe_f]; exact f.2
  have hgmem : coeffMap A.subtype (qExpand A t (jqModC A)) ∈ EE := by rw [hι_jq, ← hcoe_g]; exact g.2
  have hf_eq : f = ⟨coeffMap A.subtype (jqModC A), hfmem⟩ := Subtype.ext (by rw [hcoe_f]; exact hι_j.symm)
  have hg_eq : g = ⟨coeffMap A.subtype (qExpand A t (jqModC A)), hgmem⟩ :=
    Subtype.ext (by rw [hcoe_g]; exact hι_jq.symm)
  obtain ⟨hf₀', hresf'⟩ := hR₀res (jqModC A) hfmem
  obtain ⟨hg₀', hresg'⟩ := hR₀res (qExpand A t (jqModC A)) hgmem
  have hf₀ : f ∈ R₀.integers := by rw [hf_eq]; exact hf₀'
  have hg₀ : g ∈ R₀.integers := by rw [hg_eq]; exact hg₀'
  have hresf : ((R₀.residue ⟨f, hf₀⟩ : Fb') : LaurentSeries kk) = jqModC kk := by
    have : (⟨f, hf₀⟩ : R₀.integers) = ⟨_, hf₀'⟩ := Subtype.ext hf_eq
    rw [this, hresf', coeffMap_jqModC]
  have hresg : ((R₀.residue ⟨g, hg₀⟩ : Fb') : LaurentSeries kk) = jqModC kk ^ t := by
    have : (⟨g, hg₀⟩ : R₀.integers) = ⟨_, hg₀'⟩ := Subtype.ext hg_eq
    rw [this, hresg', ModularCurve.coeffMap_qExpand, coeffMap_jqModC, hqj]

  have hf₁ : f ∈ R₁.integers := by
    change w f ∈ R₀.integers
    rw [hwf]; exact hg₀
  have hresf₁ : ((R₁.residue ⟨f, hf₁⟩ : Fb') : LaurentSeries kk) = jqModC kk ^ t := by
    have h := transport_residue_apply A R₀ w f hf₁ (by rw [hwf]; exact hg₀)
    rw [h]
    have : (⟨w f, by rw [hwf]; exact hg₀⟩ : R₀.integers) = ⟨g, hg₀⟩ := Subtype.ext hwf
    rw [this, hresg]

  have hne : R₀.integers ≠ R₁.integers := by
    intro heq

    set e : EE := w.symm f with hedef
    have hwe : w e = f := by rw [hedef, AlgEquiv.apply_symm_apply]
    have he₁ : e ∈ R₁.integers := by
      change w e ∈ R₀.integers
      rw [hwe]; exact hf₀
    have he₀ : e ∈ R₀.integers := by rw [heq]; exact he₁

    set d : EE := e ^ t - f with hddef
    have hd₀ : d ∈ R₀.integers := sub_mem (pow_mem he₀ t) hf₀
    have hd₁ : d ∈ R₁.integers := sub_mem (pow_mem he₁ t) hf₁
    have hwd : w d = f ^ t - g := by rw [hddef, map_sub, map_pow, hwe, hwf]
    have hwd₀ : w d ∈ R₀.integers := by rw [hwd]; exact sub_mem (pow_mem hf₀ t) hg₀

    have hres₁d : R₁.residue ⟨d, hd₁⟩ = 0 := by
      have h := transport_residue_apply A R₀ w d hd₁ hwd₀
      rw [h]
      have : (⟨w d, hwd₀⟩ : R₀.integers) = ⟨f, hf₀⟩ ^ t - ⟨g, hg₀⟩ :=
        Subtype.ext (by show w d = _; rw [hwd]; rfl)
      rw [this, map_sub, map_pow]
      apply sub_eq_zero.mpr
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hresf, hresg]

    have hres₀d : R₀.residue ⟨d, hd₀⟩ = 0 := by
      by_contra hne0
      have hd_ne : d ≠ 0 := ne_zero_of_residue_ne_zero A R₀ hd₀ hne0
      have hinv₀ : d⁻¹ ∈ R₀.integers := inv_mem_of_residue_ne_zero A R₀ hd₀ hne0
      have hinv₁ : d⁻¹ ∈ R₁.integers := by rw [← heq]; exact hinv₀
      exact residue_ne_zero_of_inv_mem A R₁ hd_ne hd₁ hinv₁ hres₁d

    have hpow : ((R₀.residue ⟨e, he₀⟩ : Fb') : LaurentSeries kk) ^ t = jqModC kk := by
      have : (⟨d, hd₀⟩ : R₀.integers) = ⟨e, he₀⟩ ^ t - ⟨f, hf₀⟩ := Subtype.ext rfl
      rw [this, map_sub, map_pow, sub_eq_zero] at hres₀d
      have h' := congrArg (fun z : Fb' => (z : LaurentSeries kk)) hres₀d
      simp only [SubmonoidClass.coe_pow] at h'
      rw [h', hresf]
    exact pow_ne_jqModC kk t ht1 _ hpow

  let R : Fin 2 → RegularProlongation A EE Fb' := ![R₀, R₁]
  have hR : Function.Injective fun i => (R i).integers := by
    have key : ∀ i j : Fin 2, (R i).integers = (R j).integers → i = j :=
      Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨fun _ => rfl, fun h => absurd h hne⟩,
        Fin.forall_fin_two.mpr ⟨fun h => absurd h.symm hne, fun _ => rfl⟩⟩
    exact fun i j h => key i j h
  have hf : ∀ i, f ∈ (R i).integers := Fin.forall_fin_two.mpr ⟨hf₀, hf₁⟩
  have hres₁ : (((R 0).residue ⟨f, hf 0⟩ : Fb') : LaurentSeries kk) = jqModC kk := hresf
  have hres₂ : (((R 1).residue ⟨f, hf 1⟩ : Fb') : LaurentSeries kk) = (jqModC kk) ^ t := hresf₁
  have htr₁ : Transcendental kk (jqModC kk) := ModularCurve.transcendental_jqModC kk
  have htr₂ : Transcendental kk ((jqModC kk) ^ t) := by
    rw [← hqj]
    exact fun h => htr₁ ((isAlgebraic_algHom_iff (qExpandAlgHomC kk t)
      (qExpand_injective (R := kk) (N := t))).mp h)
  have htr : ∀ i, Transcendental kk ((R i).residue ⟨f, hf i⟩) := by
    refine Fin.forall_fin_two.mpr ⟨fun h => htr₁ ?_, fun h => htr₂ ?_⟩
    · rw [← hres₁]
      exact (isAlgebraic_algHom_iff (Fb').val Subtype.val_injective).mpr h
    · rw [← hres₂]
      exact (isAlgebraic_algHom_iff (Fb').val Subtype.val_injective).mpr h

  set Jb : IntermediateField kk (LaurentSeries kk) :=
    IntermediateField.adjoin kk ({jqModC kk} : Set (LaurentSeries kk)) with hJbdef
  set Jbt : IntermediateField kk (LaurentSeries kk) :=
    IntermediateField.adjoin kk ({(jqModC kk) ^ t} : Set (LaurentSeries kk)) with hJbtdef
  have hJbFb : Jb ≤ (Fb) :=
    adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem_qExpFunctionFieldC kk _))
  have hJbtJb : Jbt ≤ Jb := adjoin_pow_le kk t
  have hFbFb' := Fb_le_Fb' M H t A

  have hup : Module.finrank (IntermediateField.adjoin ℚ̄ ({f} : Set EE)) EE ≤
      (CohCarrier.GammaH M (Hpm M H)).index * (Gamma0 t).index :=
    (ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index ℚ̄
      (Gam' M H t) (T_mem_Gam' M H t) (CohCarrier.GammaH M (Hpm M H) ⊓ Gamma0 (M * t))
      (Gam'_le_pm M H t) (fun γ hγ => mem_or_neg_mem_of_mem_pm M H t hγ) f hcoe_f).trans
      (index_pm_le M H t htM)

  set xb : Fb := ⟨jqModC kk, jqModC_mem_qExpFunctionFieldC kk _⟩ with hxbdef
  have hIg : (CohCarrier.GammaH M (Hpm M H)).index ≤
      Module.finrank (IntermediateField.adjoin kk ({xb} : Set Fb)) Fb :=
    ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField M H hℓM A hA
      xb rfl
  have hconvF : Module.finrank (IntermediateField.adjoin kk ({xb} : Set Fb)) Fb =
      relfinrank Jb (Fb) := (relfinrank_adjoin_eq_finrank (Fb) xb).symm
  rw [hconvF] at hIg

  obtain ⟨x', -, -, hfd', hle'⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField ℚ̄ A
      (Gam' M H t) (T_mem_Gam' M H t)
  have hposE : 0 < Module.finrank (IntermediateField.adjoin ℚ̄ ({f} : Set EE)) EE := by
    have h1 := hle' f hcoe_f
    have h2 : 0 < Module.finrank
        (IntermediateField.adjoin kk ({x'} : Set (qExpFunctionFieldC kk (Gam' M H t))))
        (qExpFunctionFieldC kk (Gam' M H t)) := by
      haveI := hfd'; exact Module.finrank_pos
    exact lt_of_lt_of_le h2 h1
  haveI hFD : FiniteDimensional (IntermediateField.adjoin ℚ̄ ({f} : Set EE)) EE :=
    Module.finite_of_finrank_pos hposE

  obtain ⟨hfin, hsum₀⟩ := AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le A
    (fun _ : Fin 2 => ((Fb') : Type _)) R hR f hf htr
  have hfin0 := hfin 0
  have hfin1 := hfin 1
  try dsimp only at hfin0 hfin1 hsum₀
  simp only [Fin.sum_univ_two] at hsum₀

  have hconv₁ : Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨f, hf 0⟩}) Fb'
      = relfinrank Jb (Fb') :=
    (relfinrank_adjoin_eq_finrank (Fb') ((R 0).residue ⟨f, hf 0⟩)).symm.trans (by rw [hres₁])
  have hconv₂ : Module.finrank (IntermediateField.adjoin kk {(R 1).residue ⟨f, hf 1⟩}) Fb'
      = relfinrank Jbt (Fb') :=
    (relfinrank_adjoin_eq_finrank (Fb') ((R 1).residue ⟨f, hf 1⟩)).symm.trans (by rw [hres₂])
  have hpos₁ : 0 < relfinrank Jb (Fb') := by rw [← hconv₁]; haveI := hfin0; exact Module.finrank_pos
  have hpos₂ : 0 < relfinrank Jbt (Fb') := by rw [← hconv₂]; haveI := hfin1; exact Module.finrank_pos
  set I := (CohCarrier.GammaH M (Hpm M H)).index with hI
  set ψ := (Gamma0 t).index with hψdef
  have hsum : relfinrank Jb (Fb') + relfinrank Jbt (Fb') ≤ I * ψ := by
    rw [← hconv₁, ← hconv₂]; exact hsum₀.trans hup

  have htow₁ : relfinrank Jb (Fb) * relfinrank (Fb) (Fb') = relfinrank Jb (Fb') :=
    relfinrank_mul_relfinrank hJbFb hFbFb'
  have htow₂ : relfinrank Jbt Jb * relfinrank Jb (Fb') = relfinrank Jbt (Fb') :=
    relfinrank_mul_relfinrank hJbtJb (hJbFb.trans hFbFb')

  have he0 : relfinrank Jbt Jb ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at htow₂; omega
  have hte : t ≤ relfinrank Jbt Jb := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hJbtJb]
    haveI : Module.Finite Jbt (extendScalars hJbtJb) := Module.finite_of_finrank_pos (by
      rw [← IntermediateField.relfinrank_eq_finrank_of_le hJbtJb]; exact Nat.pos_of_ne_zero he0)
    exact le_finrank_adjoin_pow kk t hqj

  set dd := relfinrank Jb (Fb) with hdd
  set n₀ := relfinrank (Fb) (Fb') with hn₀
  have hI0 : 0 < I := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hdn : 0 < dd * n₀ := by rw [htow₁]; exact hpos₁
  have hd0 : 0 < dd := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_mul] at hdn; exact lt_irrefl 0 hdn
  have hn0 : 0 < n₀ := Nat.pos_of_ne_zero fun h => by
    rw [h, mul_zero] at hdn; exact lt_irrefl 0 hdn
  have hb : t * (dd * n₀) ≤ relfinrank Jbt (Fb') := by
    rw [← htow₂, htow₁]; exact Nat.mul_le_mul_right _ hte
  have hineq : dd * n₀ + t * (dd * n₀) ≤ dd * ψ := by
    calc dd * n₀ + t * (dd * n₀) ≤ relfinrank Jb (Fb') + relfinrank Jbt (Fb') := by
          rw [← htow₁]; exact Nat.add_le_add_left hb _
      _ ≤ I * ψ := hsum
      _ ≤ dd * ψ := Nat.mul_le_mul_right _ hIg
  have hn₀1 : n₀ = 1 := by
    have h1 : dd * (n₀ * (t + 1)) ≤ dd * ψ := by
      have : dd * n₀ + t * (dd * n₀) = dd * (n₀ * (t + 1)) := by ring
      rw [← this]; exact hineq
    have h2 : n₀ * (t + 1) ≤ ψ := Nat.le_of_mul_le_mul_left h1 hd0
    have h3 : n₀ * (t + 1) < 2 * (t + 1) := lt_of_le_of_lt h2 hψ
    have h4 : n₀ < 2 := Nat.lt_of_mul_lt_mul_right h3
    omega

  have hle : (Fb') ≤ (Fb) := (IntermediateField.relfinrank_eq_one_iff).mp hn₀1
  exact le_antisymm hle hFbFb'

end Main

section PrimePow

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem index_Gamma0_prime_pow_lt (r : ℕ) (hr : r ≠ 0) [NeZero (ℓ ^ r)] :
    (Gamma0 (ℓ ^ r)).index < 2 * (ℓ ^ r + 1) := by
  rw [ModularCurve.Gamma0_index, ModularCurve.dedekindPsi_prime_pow ℓ r Fact.out hr]
  have h : ℓ ^ (r - 1) ≤ ℓ ^ r := Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (Nat.sub_le r 1)
  omega

theorem case_zero (K : Type*) [Field K] :
    xHTopFunctionFieldC K N H (N * ℓ ^ 0) = xHFunctionFieldC K N H := by
  rw [pow_zero, mul_one]
  have : CohCarrier.GammaH N H ⊓ Gamma0 N = CohCarrier.GammaH N H :=
    le_antisymm inf_le_left (le_inf le_rfl (CohCarrier.GammaH_le_Gamma0 H))
  rw [xHTopFunctionFieldC, this, xHFunctionFieldC]

theorem final (hℓN : ¬ ℓ ∣ N) (r : ℕ) (hA : A.LiesOverPrime ℓ) :
    xHTopFunctionFieldC (IsLocalRing.ResidueField A) N H (N * ℓ ^ r) =
      xHFunctionFieldC (IsLocalRing.ResidueField A) N H := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact case_zero N H (ℓ := ℓ) _
  haveI hℓ0 : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : NeZero (ℓ ^ r) := ⟨pow_ne_zero _ hℓ0.ne⟩
  haveI hchar : CharP (IsLocalRing.ResidueField A) ℓ := charP_residueField ℓ A hA
  have ht1 : 1 < ℓ ^ r := Nat.one_lt_pow hr.ne' (Fact.out : ℓ.Prime).one_lt
  have htM : Nat.Coprime (ℓ ^ r) N :=
    Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓN)
  have hqj : qExpand (IsLocalRing.ResidueField A) (ℓ ^ r) (jqModC (IsLocalRing.ResidueField A)) =
      (jqModC (IsLocalRing.ResidueField A)) ^ (ℓ ^ r) :=
    qExpand_prime_pow_jqModC (IsLocalRing.ResidueField A) ℓ r
  have hψ := index_Gamma0_prime_pow_lt (ℓ := ℓ) r hr.ne'
  exact main N H (ℓ ^ r) A hℓN hA ht1 htM hqj hψ

end PrimePow

end XHTopResidueCollapsePow
p2m_reactivate "P2MW.S_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd.XHTopResidueCollapsePow"

theorem solution
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (r : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    ModularCurve.xHTopFunctionFieldC (IsLocalRing.ResidueField A) N H (N * ℓ ^ r) =
      ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) N H :=
  XHTopResidueCollapsePow.final N H A hℓN r hA

end
p2m_reactivate "P2MW.S_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd.XHTopResidueCollapsePow"

end S_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd (solution)
