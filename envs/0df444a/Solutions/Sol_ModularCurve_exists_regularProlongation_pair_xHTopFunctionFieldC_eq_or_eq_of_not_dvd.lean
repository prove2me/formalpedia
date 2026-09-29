-- Prove2me | solution 1 for ModularCurve.exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f194a5f9-4399-5182-876b-4c85ce7e009f

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_xHTopFunctionFieldC_residueField_mul_eq_xHFunctionFieldC_of_not_dvd
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical MatrixGroups
p2m_open "IntermediateField AlgebraicCurve ModularCurve~laurentBaseChange_mono~order_qExpand CongruenceSubgroup"

namespace XHTopTwoBranches

section Groups

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ)

abbrev Gam : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H

abbrev Gam' : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H ⊓ Gamma0 (M * q)

omit [NeZero M] in
theorem Gam'_le : Gam' M H q ≤ Gam M H := inf_le_left

scoped instance : (Gam M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance [NeZero q] : (Gam' M H q).FiniteIndex := by
  haveI : NeZero (M * q) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * q)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M q)).trans (Gamma1_le_GammaH M H)

omit [NeZero M] in
theorem T_mem_Gam' : ModularGroup.T ∈ Gam' M H q := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

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

variable (p : ℕ) [Fact p.Prime]

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
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      nlinarith
    · exact hc (qExpand_coeff_of_not_dvd p x hdvd)

theorem eq_zero_of_sum_eq_zero_of_order_injOn {ι : Type*} [Fintype ι] (t : ι → LaurentSeries K)
    (hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → (t i).order = (t j).order → i = j)
    (hsum : ∑ i, t i = 0) : ∀ i, t i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  set s : Finset ι := Finset.univ.filter fun i => t i ≠ 0 with hs
  have hsne : s.Nonempty := ⟨i₁, by simp [hs, hi₁]⟩
  obtain ⟨i₀, hi₀s, hmin⟩ := Finset.exists_min_image s (fun i => (t i).order) hsne
  have hi₀ : t i₀ ≠ 0 := by simpa [hs] using hi₀s
  have hcoeff : (∑ i, t i).coeff (t i₀).order = (t i₀).coeff (t i₀).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ _) h)
    by_cases hti : t i = 0
    · rw [hti, HahnSeries.coeff_zero]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      have hle := hmin i (by simp [hs, hti])
      exact lt_of_le_of_ne hle fun h => hi (hdist i i₀ hti hi₀ h.symm)
  rw [hsum, HahnSeries.coeff_zero] at hcoeff
  exact coeff_order_ne_zero' K hi₀ hcoeff.symm

theorem pow_ne_jqModC (z : LaurentSeries K) : z ^ p ≠ jqModC K := by
  intro h
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases hz : z = 0
  · rw [hz, zero_pow (Fact.out : p.Prime).ne_zero] at h
    exact jqModC_ne_zero_of_nontrivial K h.symm
  · have h1 : (z ^ p).order = ((jqModC K) ^ 1).order := by rw [h, pow_one]
    rw [HahnSeries.order_pow, order_jqModC_pow, nsmul_eq_mul] at h1
    push_cast at h1
    have h2 : (p : ℤ) ∣ 1 := ⟨-z.order, by linear_combination h1⟩
    have h3 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h2
    have h4 : (1 : ℤ) < p := by exact_mod_cast hp1
    linarith

variable [CharP K p]

theorem adjoin_pow_le :
    IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K))
      ≤ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
    (pow_mem (mem_adjoin_simple_self K (jqModC K)) p))

theorem exists_qExpand_eq_of_mem_adjoin_pow {c : LaurentSeries K}
    (hc : c ∈ IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K))) :
    ∃ d : LaurentSeries K, qExpand K p d = c := by
  have hle : Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ {(jqModC K) ^ p})
      ≤ (qExpand K p).fieldRange := by
    rw [Subfield.closure_le]
    rintro z (⟨t, rfl⟩ | rfl)
    · refine ⟨algebraMap K (LaurentSeries K) t, ?_⟩
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
    · exact ⟨jqModC K, qExpand_jqModC_eq_pow_unconditional K⟩
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
      fun i => exists_qExpand_eq_of_mem_adjoin_pow K p (g i).2
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

theorem fieldRange_val_comp_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (h : A ≤ B) :
    (B.val.comp (IntermediateField.inclusion h)).fieldRange = A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem finrankAlong_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (h : A ≤ B) :
    finrankAlong K (IntermediateField.inclusion h) = relfinrank A B := by
  rw [AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange, fieldRange_val_comp_inclusion]

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

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [Fact q.Prime]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "kk" => IsLocalRing.ResidueField A

local notation "EE" => laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * q))

local notation "KK" => laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField M H)

local notation "Fb'" => xHTopFunctionFieldC (IsLocalRing.ResidueField A) M H (M * q)

local notation "Fb" => xHFunctionFieldC (IsLocalRing.ResidueField A) M H

scoped instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

omit [NeZero M] in
theorem KK_le_EE : (KK) ≤ (EE) := laurentBaseChange_mono ℚ̄ (xHFunctionFieldC_le_top ℚ M H (M * q))

omit [NeZero M] in
theorem Fb_le_Fb' : (Fb) ≤ (Fb') := xHFunctionFieldC_le_top kk M H (M * q)

def yK : KK := ⟨jqModC ℚ̄, jqModC_mem_laurentBaseChange ℚ̄ _⟩

omit [NeZero M] in
@[scoped simp] theorem coe_yK : ((yK M H : KK) : LaurentSeries ℚ̄) = jqModC ℚ̄ := rfl

set_option maxHeartbeats 25600000 in

theorem main' (hqM : ¬ q ∣ M) (hA : A.LiesOverPrime q) :
    ∃ (R : Fin 2 → RegularProlongation A EE Fb') (w : EE ≃ₐ[ℚ̄] EE),
      (∀ x : xHFunctionFieldBar M H,
          w (heckeAlphaHBar ℚ̄ M H q x) = heckeBetaHBar ℚ̄ M H q x) ∧
      (∀ x : xHFunctionFieldBar M H,
          w (heckeBetaHBar ℚ̄ M H q x) =
            heckeAlphaHBar ℚ̄ M H q
              (diamondAutHBar M H
                (ZMod.unitOfCoprime q ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM)) x)) ∧
      (∀ f : EE, f ∈ (R 0).integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries ℚ̄) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      (∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ EE),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : EE) ∈ (R 0).integers,
          (((R 0).residue ⟨_, hint⟩ : Fb') : LaurentSeries kk) = coeffMap (IsLocalRing.residue A) y) ∧
      (∀ f : EE, f ∈ (R 1).integers ↔ w f ∈ (R 0).integers) ∧
      (∀ (f : EE) (h₁ : f ∈ (R 1).integers) (h₀ : w f ∈ (R 0).integers),
        (R 1).residue ⟨f, h₁⟩ = (R 0).residue ⟨w f, h₀⟩) ∧
      (R 0).integers ≠ (R 1).integers ∧
      (∀ f : EE, (f : LaurentSeries ℚ̄) = jqModC ℚ̄ →
        ∃ hj : ∀ i, f ∈ (R i).integers,
          (((R 0).residue ⟨f, hj 0⟩ : Fb') : LaurentSeries kk) = jqModC kk ∧
          (((R 1).residue ⟨f, hj 1⟩ : Fb') : LaurentSeries kk) = jqModC kk ^ q ∧
          Module.finrank (IntermediateField.adjoin kk {(R 1).residue ⟨f, hj 1⟩}) Fb' =
            q * Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨f, hj 0⟩}) Fb' ∧
          Module.finrank (IntermediateField.adjoin ℚ̄ ({f} : Set EE)) EE =
            (q + 1) * Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨f, hj 0⟩}) Fb') ∧
      ∀ f : EE, (f : LaurentSeries ℚ̄) = jqModC ℚ̄ →
        ∀ V : ValuationSubring EE,
          (∀ e ∈ IntermediateField.adjoin ℚ̄ ({f} : Set EE), e ∈ V ↔ e ∈ (R 0).integers) →
          V = (R 0).integers ∨ V = (R 1).integers := by
  haveI hchar : CharP kk q := charP_residueField q A hA
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hcol : (Fb') = (Fb) :=
    ModularCurve.xHTopFunctionFieldC_residueField_mul_eq_xHFunctionFieldC_of_not_dvd M H hqM A hA

  have hin : HeckeDiamondInputsHAll M H := ModularCurve.heckeDiamondInputsHAll M H
  have hβdef : HeckeBetaHDefined M H q := (hin.heckeInputsHAlong q Fact.out).betaHDefined
  obtain ⟨w, hwα, hwβ⟩ :=
    ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar M H (ℓ := q) hqM hin
  obtain ⟨R₀, hR₀mem, hR₀res⟩ : ∃ R₀ : RegularProlongation A EE Fb',
      (∀ f : EE, f ∈ R₀.integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries ℚ̄) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ EE),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : EE) ∈ R₀.integers,
          ((R₀.residue ⟨_, hO⟩ : Fb') : LaurentSeries kk) = coeffMap (IsLocalRing.residue A) y := by
    obtain ⟨R₀, h1, h2⟩ :=
      ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC ℚ̄ A
        (Gam' M H q) (T_mem_Gam' M H q)
    exact ⟨R₀, h1, h2⟩
  let R₁ : RegularProlongation A EE Fb' := transport A R₀ w

  set f₀ : EE := heckeAlphaHBar ℚ̄ M H q (yK M H) with hf₀def
  set g : EE := heckeBetaHBar ℚ̄ M H q (yK M H) with hgdef
  have hcoe_f : (f₀ : LaurentSeries ℚ̄) = jqModC ℚ̄ := by
    rw [hf₀def, coe_heckeAlphaHBar]; rfl
  have hcoe_g : (g : LaurentSeries ℚ̄) = qExpand ℚ̄ q (jqModC ℚ̄) := by
    rw [hgdef, coe_heckeBetaHBar M H q hβdef]; rfl
  have hwf : w f₀ = g := hwα (yK M H)

  have hι_j : coeffMap A.subtype (jqModC A) = jqModC ℚ̄ := coeffMap_jqModC _
  have hι_jq : coeffMap A.subtype (qExpand A q (jqModC A)) = qExpand ℚ̄ q (jqModC ℚ̄) := by
    rw [coeffMap_qExpand, coeffMap_jqModC]
  have hfmem : coeffMap A.subtype (jqModC A) ∈ EE := by rw [hι_j, ← hcoe_f]; exact f₀.2
  have hgmem : coeffMap A.subtype (qExpand A q (jqModC A)) ∈ EE := by rw [hι_jq, ← hcoe_g]; exact g.2
  have hf_eq : f₀ = ⟨coeffMap A.subtype (jqModC A), hfmem⟩ := Subtype.ext (by rw [hcoe_f]; exact hι_j.symm)
  have hg_eq : g = ⟨coeffMap A.subtype (qExpand A q (jqModC A)), hgmem⟩ :=
    Subtype.ext (by rw [hcoe_g]; exact hι_jq.symm)
  obtain ⟨hf₀', hresf'⟩ := hR₀res (jqModC A) hfmem
  obtain ⟨hg₀', hresg'⟩ := hR₀res (qExpand A q (jqModC A)) hgmem
  have hf₀ : f₀ ∈ R₀.integers := by rw [hf_eq]; exact hf₀'
  have hg₀ : g ∈ R₀.integers := by rw [hg_eq]; exact hg₀'
  have hresf : ((R₀.residue ⟨f₀, hf₀⟩ : Fb') : LaurentSeries kk) = jqModC kk := by
    have : (⟨f₀, hf₀⟩ : R₀.integers) = ⟨_, hf₀'⟩ := Subtype.ext hf_eq
    rw [this, hresf', coeffMap_jqModC]
  have hresg : ((R₀.residue ⟨g, hg₀⟩ : Fb') : LaurentSeries kk) = jqModC kk ^ q := by
    have : (⟨g, hg₀⟩ : R₀.integers) = ⟨_, hg₀'⟩ := Subtype.ext hg_eq
    rw [this, hresg', coeffMap_qExpand, coeffMap_jqModC, qExpand_jqModC_eq_pow_unconditional kk]

  have hf₁ : f₀ ∈ R₁.integers := by
    change w f₀ ∈ R₀.integers
    rw [hwf]; exact hg₀
  have hresf₁ : ((R₁.residue ⟨f₀, hf₁⟩ : Fb') : LaurentSeries kk) = jqModC kk ^ q := by
    have h := transport_residue_apply A R₀ w f₀ hf₁ (by rw [hwf]; exact hg₀)
    rw [h]
    have : (⟨w f₀, by rw [hwf]; exact hg₀⟩ : R₀.integers) = ⟨g, hg₀⟩ := Subtype.ext hwf
    rw [this, hresg]

  have hne : R₀.integers ≠ R₁.integers := by
    intro heq
    set e' : EE := w.symm f₀ with hedef
    have hwe : w e' = f₀ := by rw [hedef, AlgEquiv.apply_symm_apply]
    have he₁ : e' ∈ R₁.integers := by
      change w e' ∈ R₀.integers
      rw [hwe]; exact hf₀
    have he₀ : e' ∈ R₀.integers := by rw [heq]; exact he₁
    set d : EE := e' ^ q - f₀ with hddef
    have hd₀ : d ∈ R₀.integers := sub_mem (pow_mem he₀ q) hf₀
    have hd₁ : d ∈ R₁.integers := sub_mem (pow_mem he₁ q) hf₁
    have hwd : w d = f₀ ^ q - g := by rw [hddef, map_sub, map_pow, hwe, hwf]
    have hwd₀ : w d ∈ R₀.integers := by rw [hwd]; exact sub_mem (pow_mem hf₀ q) hg₀
    have hres₁d : R₁.residue ⟨d, hd₁⟩ = 0 := by
      have h := transport_residue_apply A R₀ w d hd₁ hwd₀
      rw [h]
      have : (⟨w d, hwd₀⟩ : R₀.integers) = ⟨f₀, hf₀⟩ ^ q - ⟨g, hg₀⟩ :=
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
    have hpow : ((R₀.residue ⟨e', he₀⟩ : Fb') : LaurentSeries kk) ^ q = jqModC kk := by
      have : (⟨d, hd₀⟩ : R₀.integers) = ⟨e', he₀⟩ ^ q - ⟨f₀, hf₀⟩ := Subtype.ext rfl
      rw [this, map_sub, map_pow, sub_eq_zero] at hres₀d
      have h' := congrArg (fun z : Fb' => (z : LaurentSeries kk)) hres₀d
      simp only [SubmonoidClass.coe_pow] at h'
      rw [h', hresf]
    exact pow_ne_jqModC kk q _ hpow

  let R : Fin 2 → RegularProlongation A EE Fb' := ![R₀, R₁]
  have hR : Function.Injective fun i => (R i).integers := by
    have key : ∀ i j : Fin 2, (R i).integers = (R j).integers → i = j :=
      Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨fun _ => rfl, fun h => absurd h hne⟩,
        Fin.forall_fin_two.mpr ⟨fun h => absurd h.symm hne, fun _ => rfl⟩⟩
    exact fun i j h => key i j h
  have hf : ∀ i, f₀ ∈ (R i).integers := Fin.forall_fin_two.mpr ⟨hf₀, hf₁⟩
  have hres₁ : (((R 0).residue ⟨f₀, hf 0⟩ : Fb') : LaurentSeries kk) = jqModC kk := hresf
  have hres₂ : (((R 1).residue ⟨f₀, hf 1⟩ : Fb') : LaurentSeries kk) = (jqModC kk) ^ q := hresf₁
  have htr₁ : Transcendental kk (jqModC kk) := ModularCurve.transcendental_jqModC kk
  have htr₂ : Transcendental kk ((jqModC kk) ^ q) := by
    rw [← qExpand_jqModC_eq_pow_unconditional kk]
    exact fun h => htr₁ ((isAlgebraic_algHom_iff (qExpandAlgHomC kk q)
      (qExpand_injective (R := kk) (N := q))).mp h)
  have htr : ∀ i, Transcendental kk ((R i).residue ⟨f₀, hf i⟩) := by
    refine Fin.forall_fin_two.mpr ⟨fun h => htr₁ ?_, fun h => htr₂ ?_⟩
    · rw [← hres₁]
      exact (isAlgebraic_algHom_iff (Fb').val Subtype.val_injective).mpr h
    · rw [← hres₂]
      exact (isAlgebraic_algHom_iff (Fb').val Subtype.val_injective).mpr h

  set Jt : IntermediateField ℚ̄ (LaurentSeries ℚ̄) :=
    IntermediateField.adjoin ℚ̄ ({jqModC ℚ̄} : Set (LaurentSeries ℚ̄)) with hJtdef
  set Jb : IntermediateField kk (LaurentSeries kk) :=
    IntermediateField.adjoin kk ({jqModC kk} : Set (LaurentSeries kk)) with hJbdef
  set Jbq : IntermediateField kk (LaurentSeries kk) :=
    IntermediateField.adjoin kk ({(jqModC kk) ^ q} : Set (LaurentSeries kk)) with hJbqdef
  have hJtKK : Jt ≤ (KK) := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (yK M H).2)
  have hFbFb' := Fb_le_Fb' M H q A
  have hJbFb : Jb ≤ (Fb) :=
    adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem_qExpFunctionFieldC kk _))
  have hJbFb' : Jb ≤ (Fb') := hJbFb.trans hFbFb'
  have hJbqJb : Jbq ≤ Jb := adjoin_pow_le kk q
  have hKKEE := KK_le_EE M H q

  have hEK : relfinrank (KK) (EE) = q + 1 := by
    rw [← finrankAlong_inclusion hKKEE, ← heckeAlphaHBar_eq_inclusion M H q hKKEE]
    exact ModularCurve.finrankAlong_heckeAlphaHBar ℚ̄ M H hqM

  set xb : Fb := ⟨jqModC kk, jqModC_mem_qExpFunctionFieldC kk _⟩ with hxbdef
  have hIg₀ : Module.finrank (IntermediateField.adjoin ℚ̄ ({yK M H} : Set KK)) KK ≤
      Module.finrank (IntermediateField.adjoin kk ({xb} : Set Fb)) Fb :=
    ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd M H hqM A hA
      xb (yK M H) rfl rfl
  have hconvK : Module.finrank (IntermediateField.adjoin ℚ̄ ({yK M H} : Set KK)) KK =
      relfinrank Jt (KK) := (relfinrank_adjoin_eq_finrank (KK) (yK M H)).symm
  have hconvF : Module.finrank (IntermediateField.adjoin kk ({xb} : Set Fb)) Fb =
      relfinrank Jb (Fb) := (relfinrank_adjoin_eq_finrank (Fb) xb).symm
  have hcolrk : relfinrank Jb (Fb) = relfinrank Jb (Fb') := by rw [hcol]
  have hIg : relfinrank Jt (KK) ≤ relfinrank Jb (Fb') := by
    rw [← hcolrk, ← hconvK, ← hconvF]; exact hIg₀

  have hconvE : Module.finrank (IntermediateField.adjoin ℚ̄ ({f₀} : Set EE)) EE = relfinrank Jt (EE) :=
    (relfinrank_adjoin_eq_finrank (EE) f₀).symm.trans (by rw [hcoe_f])
  have htowE : relfinrank Jt (KK) * relfinrank (KK) (EE) = relfinrank Jt (EE) :=
    relfinrank_mul_relfinrank hJtKK hKKEE
  obtain ⟨x', -, -, hfd', hle'⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField ℚ̄ A
      (Gam' M H q) (T_mem_Gam' M H q)
  have hposE : 0 < Module.finrank (IntermediateField.adjoin ℚ̄ ({f₀} : Set EE)) EE := by
    have h1 := hle' f₀ hcoe_f
    have h2 : 0 < Module.finrank
        (IntermediateField.adjoin kk ({x'} : Set (qExpFunctionFieldC kk (Gam' M H q))))
        (qExpFunctionFieldC kk (Gam' M H q)) := by
      haveI := hfd'; exact Module.finrank_pos
    exact lt_of_lt_of_le h2 h1
  haveI hFD : FiniteDimensional (IntermediateField.adjoin ℚ̄ ({f₀} : Set EE)) EE :=
    Module.finite_of_finrank_pos hposE

  obtain ⟨hfin, hsum₀⟩ := AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le A
    (fun _ : Fin 2 => ((Fb') : Type _)) R hR f₀ hf htr
  have hfin0 := hfin 0
  have hfin1 := hfin 1
  try dsimp only at hfin0 hfin1 hsum₀
  simp only [Fin.sum_univ_two] at hsum₀

  have hconv₁ : Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨f₀, hf 0⟩}) Fb'
      = relfinrank Jb (Fb') :=
    (relfinrank_adjoin_eq_finrank (Fb') ((R 0).residue ⟨f₀, hf 0⟩)).symm.trans (by rw [hres₁])
  have hconv₂ : Module.finrank (IntermediateField.adjoin kk {(R 1).residue ⟨f₀, hf 1⟩}) Fb'
      = relfinrank Jbq (Fb') :=
    (relfinrank_adjoin_eq_finrank (Fb') ((R 1).residue ⟨f₀, hf 1⟩)).symm.trans (by rw [hres₂])
  have hpos₁ : 0 < relfinrank Jb (Fb') := by rw [← hconv₁]; haveI := hfin0; exact Module.finrank_pos
  have hpos₂ : 0 < relfinrank Jbq (Fb') := by rw [← hconv₂]; haveI := hfin1; exact Module.finrank_pos
  have hsum : relfinrank Jb (Fb') + relfinrank Jbq (Fb') ≤ relfinrank Jt (KK) * (q + 1) := by
    rw [← hconv₁, ← hconv₂, ← hEK, htowE, ← hconvE]; exact hsum₀

  have htow₂ : relfinrank Jbq Jb * relfinrank Jb (Fb') = relfinrank Jbq (Fb') :=
    relfinrank_mul_relfinrank hJbqJb hJbFb'

  have he0 : relfinrank Jbq Jb ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at htow₂; omega
  have hqe : q ≤ relfinrank Jbq Jb := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hJbqJb]
    haveI : Module.Finite Jbq (extendScalars hJbqJb) := Module.finite_of_finrank_pos (by
      rw [← IntermediateField.relfinrank_eq_finrank_of_le hJbqJb]; exact Nat.pos_of_ne_zero he0)
    exact le_finrank_adjoin_pow kk q

  set dd := relfinrank Jb (Fb') with hdd
  set r := relfinrank Jbq Jb with hr
  set c := relfinrank Jt (KK) with hc
  have hb : q * dd ≤ relfinrank Jbq (Fb') := by rw [← htow₂]; exact Nat.mul_le_mul_right _ hqe
  have hineq : dd + q * dd ≤ c * (q + 1) :=
    le_trans (Nat.add_le_add_left hb _) hsum
  have hcd : c = dd := by
    apply le_antisymm hIg
    have h1 : (q + 1) * dd ≤ (q + 1) * c := by
      have : dd + q * dd = (q + 1) * dd := by ring
      rw [← this, mul_comm (q + 1) c]; exact hineq
    exact Nat.le_of_mul_le_mul_left h1 (Nat.succ_pos q)
  have hrq : r = q := by
    apply le_antisymm _ hqe
    have h1 : r * dd ≤ q * dd := by
      rw [htow₂]
      have h2 : dd + relfinrank Jbq (Fb') ≤ dd * (q + 1) := hcd ▸ hsum
      nlinarith
    exact Nat.le_of_mul_le_mul_right h1 hpos₁
  have hbq : relfinrank Jbq (Fb') = q * dd := by rw [← htow₂, hrq]
  have hEd : Module.finrank (IntermediateField.adjoin ℚ̄ ({f₀} : Set EE)) EE = (q + 1) * dd := by
    rw [hconvE, ← htowE, hEK, hcd, mul_comm]
  have hdeg₁ : Module.finrank (IntermediateField.adjoin kk {(R 1).residue ⟨f₀, hf 1⟩}) Fb'
      = q * Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨f₀, hf 0⟩}) Fb' := by
    rw [hconv₁, hconv₂, hbq]
  have hdegE : Module.finrank (IntermediateField.adjoin ℚ̄ ({f₀} : Set EE)) EE
      = (q + 1) * Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨f₀, hf 0⟩}) Fb' := by
    rw [hconv₁, hEd]

  have heq : ∑ i, Module.finrank (IntermediateField.adjoin kk
        ({(R i).residue ⟨f₀, hf i⟩} : Set Fb')) Fb'
      = Module.finrank (IntermediateField.adjoin ℚ̄ ({f₀} : Set EE)) EE := by
    rw [Fin.sum_univ_two, hdegE, hdeg₁]; ring
  have hcomplete : ∀ V : ValuationSubring EE,
      (∀ e ∈ IntermediateField.adjoin ℚ̄ ({f₀} : Set EE), e ∈ V ↔ e ∈ R₀.integers) →
      V = R₀.integers ∨ V = R₁.integers := by
    intro V hV
    obtain ⟨i, hi⟩ :=
      AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
        A (fun _ : Fin 2 => ((Fb') : Type _)) R hR f₀ hf htr heq 0 V hV
    revert hi
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hi; exact Or.inl hi
    · intro hi
      have : i = 0 := Subsingleton.elim _ _
      subst this
      exact Or.inr hi

  refine ⟨R, w, hwα, hwβ, hR₀mem, hR₀res, fun f => Iff.rfl, fun f h₁ h₀ => rfl, hne, ?_, ?_⟩
  · intro f hfj
    have hff : f = f₀ := Subtype.ext (by rw [hfj, hcoe_f])
    subst hff
    exact ⟨hf, hres₁, hres₂, hdeg₁, hdegE⟩
  · intro f hfj V hV
    have hff : f = f₀ := Subtype.ext (by rw [hfj, hcoe_f])
    subst hff
    exact hcomplete V hV

set_option maxHeartbeats 12800000 in

theorem main (hqM : ¬ q ∣ M) (hA : A.LiesOverPrime q) :
    ∃ (R : Fin 2 → RegularProlongation A EE Fb) (w : EE ≃ₐ[ℚ̄] EE),
      (∀ x : xHFunctionFieldBar M H,
          w (heckeAlphaHBar ℚ̄ M H q x) = heckeBetaHBar ℚ̄ M H q x) ∧
      (∀ x : xHFunctionFieldBar M H,
          w (heckeBetaHBar ℚ̄ M H q x) =
            heckeAlphaHBar ℚ̄ M H q
              (diamondAutHBar M H
                (ZMod.unitOfCoprime q ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM)) x)) ∧
      (∀ f : EE, f ∈ (R 0).integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries ℚ̄) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      (∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ EE),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : EE) ∈ (R 0).integers,
          (((R 0).residue ⟨_, hint⟩ : Fb) : LaurentSeries kk) = coeffMap (IsLocalRing.residue A) y) ∧
      (∀ f : EE, f ∈ (R 1).integers ↔ w f ∈ (R 0).integers) ∧
      (∀ (f : EE) (h₁ : f ∈ (R 1).integers) (h₀ : w f ∈ (R 0).integers),
        (R 1).residue ⟨f, h₁⟩ = (R 0).residue ⟨w f, h₀⟩) ∧
      (R 0).integers ≠ (R 1).integers ∧
      (∀ f : EE, (f : LaurentSeries ℚ̄) = jqModC ℚ̄ →
        ∃ hj : ∀ i, f ∈ (R i).integers,
          (((R 0).residue ⟨f, hj 0⟩ : Fb) : LaurentSeries kk) = jqModC kk ∧
          (((R 1).residue ⟨f, hj 1⟩ : Fb) : LaurentSeries kk) = jqModC kk ^ q ∧
          Module.finrank (IntermediateField.adjoin kk {(R 1).residue ⟨f, hj 1⟩}) Fb =
            q * Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨f, hj 0⟩}) Fb ∧
          Module.finrank (IntermediateField.adjoin ℚ̄ ({f} : Set EE)) EE =
            (q + 1) * Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨f, hj 0⟩}) Fb) ∧
      ∀ f : EE, (f : LaurentSeries ℚ̄) = jqModC ℚ̄ →
        ∀ V : ValuationSubring EE,
          (∀ e ∈ IntermediateField.adjoin ℚ̄ ({f} : Set EE), e ∈ V ↔ e ∈ (R 0).integers) →
          V = (R 0).integers ∨ V = (R 1).integers := by
  have h := main' M H q A hqM hA
  rw [ModularCurve.xHTopFunctionFieldC_residueField_mul_eq_xHFunctionFieldC_of_not_dvd M H hqM A hA] at h
  exact h

end Main

end XHTopTwoBranches
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd.XHTopTwoBranches"

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {q : ℕ} [Fact q.Prime] (hqM : ¬ q ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ (R : Fin 2 → AlgebraicCurve.RegularProlongation A
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))
        (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H))
      (w : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)) ≃ₐ[AlgebraicClosure ℚ]
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),

      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H q x) =
            ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H q x) ∧
      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H q x) =
            ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H q
              (ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime q ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM)) x)) ∧

      (∀ f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)),
        f ∈ (R 0).integers ↔
          ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y =
              ModularCurve.coeffMap A.subtype x) ∧

      (∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),
        ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))) ∈ (R 0).integers,
          (((R 0).residue ⟨_, hint⟩ :
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y) ∧

      (∀ f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)),
        f ∈ (R 1).integers ↔ w f ∈ (R 0).integers) ∧
      (∀ (f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))
        (h₁ : f ∈ (R 1).integers) (h₀ : w f ∈ (R 0).integers),
        (R 1).residue ⟨f, h₁⟩ = (R 0).residue ⟨w f, h₀⟩) ∧

      (R 0).integers ≠ (R 1).integers ∧

      (∀ (f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
        ∃ hj : ∀ i, f ∈ (R i).integers,
          (((R 0).residue ⟨f, hj 0⟩ :
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.jqModC (IsLocalRing.ResidueField A) ∧
          (((R 1).residue ⟨f, hj 1⟩ :
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.jqModC (IsLocalRing.ResidueField A) ^ q ∧
          Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              {(R 1).residue ⟨f, hj 1⟩})
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) =
          q * Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              {(R 0).residue ⟨f, hj 0⟩})
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) ∧
          Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({f} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
                (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))))
            (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))) =
          (q + 1) * Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              {(R 0).residue ⟨f, hj 0⟩})
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)) ∧

      ∀ (f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
        ∀ V : ValuationSubring (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))),
          (∀ e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({f} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
                (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))),
            e ∈ V ↔ e ∈ (R 0).integers) →
          V = (R 0).integers ∨ V = (R 1).integers :=
  XHTopTwoBranches.main M H q A hqM hA

end
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd.XHTopTwoBranches"

end S_ModularCurve_exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd (solution)
