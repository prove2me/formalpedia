-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/46e28646-bf81-52a4-9cd3-e5c437410c82

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_HeckeOperatorTotal
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_heckeDivBar_single_pt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane AlgebraicCurve ModularForm
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "ComplexPlaceDictionary modularFunctionFieldFull laurentBaseChange clamp01_of_mem segmentPoint continuous_segmentPoint segmentPath coe_segmentPath intervalIntegrable_periodIntegrand periodAlong periodAlong_apply periodLattice cuspHeckeGen_of_dvd cuspHeckeGen_of_not_dvd cuspHeckeRep cuspHeckeRep_heckeGen dualHeckeRep dualHeckeRep_apply_apply heckeGen HeckeAlphaBarIntegral HeckeBetaBarIntegral heckeDivBar exists_hasEquivariantPrimitive isCurveOver_laurentBaseChange_modularFunctionFieldFull ComplexPlaceDictionary.heckeDivBar_single_pt"
namespace HeckeAbelJacobiGlue
p2m_open "ModularCurve"

section FTC

theorem hasDerivAt_affine (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a + (s : ℂ) * b) (b - a) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a) (-(1 : ℂ) * a) t := by
    simpa using ((hasDerivAt_const t (1 : ℂ)).sub h1).mul_const a
  have h3 : HasDerivAt (fun s : ℝ => (s : ℂ) * b) (1 * b) t := h1.mul_const b
  have := h2.add h3
  convert this using 1 <;> first | rfl | exact Subsingleton.elim _ _ | ring

theorem segmentPoint_eq_of_mem {τ₀ τ₁ : ℍ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ModularCurve.segmentPoint τ₀ τ₁ t = (1 - (t : ℂ)) * (τ₀ : ℂ) + (t : ℂ) * (τ₁ : ℂ) := by
  simp only [ModularCurve.segmentPoint, ModularCurve.clamp01_of_mem ht, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem periodAlong_eq_sub (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    {F : ℍ → ℂ} (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlong N τ₀ τ₁ f = F τ₁ - F τ₀ := by
  rw [ModularCurve.periodAlong_apply]
  set g : ℝ → ℂ := fun t => F (ModularCurve.segmentPath τ₀ τ₁ t) with hg
  have hgF : ∀ t, g t = (F ∘ ofComplex) (ModularCurve.segmentPoint τ₀ τ₁ t) := by
    intro t
    simp only [hg, Function.comp]
    congr 1
    rw [← ModularCurve.coe_segmentPath, ofComplex_apply]
  have hg0 : g 0 = F τ₀ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 0 = (τ₀ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨le_rfl, zero_le_one⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hg1 : g 1 = F τ₁ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 1 = (τ₁ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨zero_le_one, le_rfl⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hFcont : ∀ τ : ℍ, ContinuousAt (F ∘ ofComplex) (τ : ℂ) := fun τ => (hF τ).continuousAt
  have hgcont : Continuous g := by
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    refine continuous_iff_continuousAt.mpr fun t => ?_
    refine ContinuousAt.comp ?_ (ModularCurve.continuous_segmentPoint τ₀ τ₁).continuousAt
    have := hFcont (ModularCurve.segmentPath τ₀ τ₁ t)
    rwa [ModularCurve.coe_segmentPath] at this
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g (f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := by
    intro t ht
    have hpath : HasDerivAt (ModularCurve.segmentPoint τ₀ τ₁) ((τ₁ : ℂ) - τ₀) t := by
      refine (hasDerivAt_affine (τ₀ : ℂ) (τ₁ : ℂ) t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact segmentPoint_eq_of_mem (Set.Ioo_subset_Icc_self hs)
    have hFat : HasDerivAt (F ∘ ofComplex) (f (ModularCurve.segmentPath τ₀ τ₁ t))
        (ModularCurve.segmentPoint τ₀ τ₁ t) := by
      have := hF (ModularCurve.segmentPath τ₀ τ₁ t)
      rwa [ModularCurve.coe_segmentPath] at this
    have hcomp := hFat.comp t hpath
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    exact hcomp
  have hint : IntervalIntegrable
      (fun t => f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) MeasureTheory.volume 0 1 :=
    ModularCurve.intervalIntegrable_periodIntegrand N τ₀ τ₁ f 0 1
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hgcont.continuousOn hderiv hint
  rw [key, hg0, hg1]

end FTC

section HeckePrimitive

variable {p : ℕ} {F f : ℍ → ℂ}

theorem heckeMatrix_smul_ofComplex (hp : p ≠ 0) (j : ℕ) {z : ℂ} (hz : 0 < z.im) :
    (heckeMatrix p j • ofComplex z : ℍ) = ofComplex (((z : ℂ) + j) / p) := by
  have h := coe_heckeMatrix_smul hp j (ofComplex z)
  rw [ofComplex_apply_of_im_pos hz] at h ⊢
  have him : 0 < (((z : ℂ) + j) / p : ℂ).im := by
    have := (heckeMatrix p j • (⟨z, hz⟩ : ℍ)).im_pos
    rwa [← UpperHalfPlane.coe_im, h] at this
  rw [ofComplex_apply_of_im_pos him]
  exact UpperHalfPlane.ext h

theorem heckeDiagMatrix_smul_ofComplex (hp : p ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    (heckeDiagMatrix p • ofComplex z : ℍ) = ofComplex ((p : ℂ) * z) := by
  have h := coe_heckeDiagMatrix_smul hp (ofComplex z)
  rw [ofComplex_apply_of_im_pos hz] at h ⊢
  have him : 0 < ((p : ℂ) * z : ℂ).im := by
    have := (heckeDiagMatrix p • (⟨z, hz⟩ : ℍ)).im_pos
    rwa [← UpperHalfPlane.coe_im, h] at this
  rw [ofComplex_apply_of_im_pos him]
  exact UpperHalfPlane.ext h

theorem hasDerivAt_comp_heckeMatrix (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ)
    (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    HasDerivAt ((fun z : ℍ => F (heckeMatrix p j • z)) ∘ ofComplex)
      ((p : ℂ)⁻¹ * f (heckeMatrix p j • τ)) ↑τ := by
  have hlin : HasDerivAt (fun z : ℂ => (z + j) / p) ((p : ℂ)⁻¹) (τ : ℂ) := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id (τ : ℂ)).add_const (j : ℂ)).div_const (p : ℂ)
  have hout : HasDerivAt (F ∘ ofComplex) (f (heckeMatrix p j • τ)) (((τ : ℂ) + j) / p) := by
    have := hF (heckeMatrix p j • τ)
    rwa [coe_heckeMatrix_smul hp] at this
  have hcomp := hout.comp (τ : ℂ) hlin
  rw [mul_comm] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  simp only [Function.comp_apply]
  rw [heckeMatrix_smul_ofComplex hp j hz]

theorem hasDerivAt_comp_heckeDiagMatrix (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ)
    (hp : p ≠ 0) (τ : ℍ) :
    HasDerivAt ((fun z : ℍ => F (heckeDiagMatrix p • z)) ∘ ofComplex)
      ((p : ℂ) * f (heckeDiagMatrix p • τ)) ↑τ := by
  have hlin : HasDerivAt (fun z : ℂ => (p : ℂ) * z) (p : ℂ) (τ : ℂ) := by
    simpa using (hasDerivAt_id (τ : ℂ)).const_mul (p : ℂ)
  have hout : HasDerivAt (F ∘ ofComplex) (f (heckeDiagMatrix p • τ)) ((p : ℂ) * τ) := by
    have := hF (heckeDiagMatrix p • τ)
    rwa [coe_heckeDiagMatrix_smul hp] at this
  have hcomp := hout.comp (τ : ℂ) hlin
  rw [mul_comm] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  simp only [Function.comp_apply]
  rw [heckeDiagMatrix_smul_ofComplex hp hz]

theorem hasDerivAt_heckeU_primitive (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ)
    (hp : p ≠ 0) (τ : ℍ) :
    HasDerivAt ((fun z : ℍ => ∑ j ∈ Finset.range p, F (heckeMatrix p j • z)) ∘ ofComplex)
      (heckeU 2 p f τ) ↑τ := by
  rw [heckeU_apply 2 hp, Finset.mul_sum]
  have := HasDerivAt.sum (u := Finset.range p) (x := (τ : ℂ))
    (A := fun j z => ((fun z : ℍ => F (heckeMatrix p j • z)) ∘ ofComplex) z)
    (A' := fun j => (p : ℂ)⁻¹ * f (heckeMatrix p j • τ))
    fun j _ => hasDerivAt_comp_heckeMatrix hF hp j τ
  convert this using 1 <;> first | rfl | exact Subsingleton.elim _ _ | (funext z; simp only [Function.comp_apply, Finset.sum_apply])

theorem hasDerivAt_heckeT_primitive (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ)
    (hp : p ≠ 0) (τ : ℍ) :
    HasDerivAt
      ((fun z : ℍ => ∑ j ∈ Finset.range p, F (heckeMatrix p j • z) + F (heckeDiagMatrix p • z)) ∘
        ofComplex)
      (heckeT 2 p f τ) ↑τ := by
  have h1 : (p : ℂ) ^ ((2 : ℤ) - 1) = p := by norm_num
  rw [heckeT_eq_heckeU_add, Pi.add_apply, slash_heckeDiagMatrix_apply 2 hp, h1]
  exact (hasDerivAt_heckeU_primitive hF hp τ).add (hasDerivAt_comp_heckeDiagMatrix hF hp τ)

end HeckePrimitive

section AJ

def lift (N ℓ : ℕ) (τ : ℍ) : ℍ →₀ ℤ :=
  ∑ j ∈ Finset.range ℓ, Finsupp.single (heckeMatrix ℓ j • τ) 1 +
    if ℓ ∣ N then 0 else Finsupp.single (heckeDiagMatrix ℓ • τ) 1

def liftHom (N ℓ : ℕ) : (ℍ →₀ ℤ) →+ (ℍ →₀ ℤ) :=
  Finsupp.liftAddHom fun τ => zmultiplesHom _ (lift N ℓ τ)

@[scoped simp]
theorem liftHom_single (N ℓ : ℕ) (τ : ℍ) (n : ℤ) :
    liftHom N ℓ (Finsupp.single τ n) = n • lift N ℓ τ := by
  simp [liftHom]

def heckePrim (N ℓ : ℕ) (F : ℍ → ℂ) (z : ℍ) : ℂ :=
  ∑ j ∈ Finset.range ℓ, F (heckeMatrix ℓ j • z) + if ℓ ∣ N then 0 else F (heckeDiagMatrix ℓ • z)

variable (N : ℕ)

def aj : (ℍ →₀ ℤ) →+ Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  Finsupp.liftAddHom fun τ => zmultiplesHom _ (ModularCurve.periodAlong N I τ)

theorem aj_apply (c : ℍ →₀ ℤ) :
    aj N c = c.sum fun τ n => n • ModularCurve.periodAlong N I τ := by
  simp only [aj, Finsupp.liftAddHom_apply]
  rfl

@[scoped simp]
theorem aj_single (τ : ℍ) (n : ℤ) : aj N (Finsupp.single τ n) = n • ModularCurve.periodAlong N I τ := by
  simp [aj_apply]

theorem aj_lift_apply (ℓ : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    aj N (lift N ℓ τ) f =
      ∑ j ∈ Finset.range ℓ, (F (heckeMatrix ℓ j • τ) - F I) +
        if ℓ ∣ N then 0 else F (heckeDiagMatrix ℓ • τ) - F I := by
  simp only [lift, map_add, map_sum, aj_single, one_smul, LinearMap.add_apply,
    LinearMap.coe_sum, Finset.sum_apply, periodAlong_eq_sub N f hF]
  split_ifs with h
  · simp
  · simp [periodAlong_eq_sub N f hF]

variable [NeZero N]

theorem hasDerivAt_heckePrim (ℓ : ℕ) [Fact ℓ.Prime] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    {F : ℍ → ℂ} (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt (heckePrim N ℓ F ∘ ofComplex)
      ((ModularCurve.cuspHeckeRep N (ModularCurve.heckeGen ⟨ℓ, Fact.out⟩) f) τ) ↑τ := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  rw [ModularCurve.cuspHeckeRep_heckeGen]
  by_cases h : ℓ ∣ N
  · rw [ModularCurve.cuspHeckeGen_of_dvd N ⟨ℓ, Fact.out⟩ h, CuspForm.coe_heckeULin_apply]
    have : heckePrim N ℓ F = fun z : ℍ => ∑ j ∈ Finset.range ℓ, F (heckeMatrix ℓ j • z) := by
      funext z; simp [heckePrim, h]
    rw [this]
    exact hasDerivAt_heckeU_primitive hF hℓ τ
  · rw [ModularCurve.cuspHeckeGen_of_not_dvd N ⟨ℓ, Fact.out⟩ h, CuspForm.coe_heckeTLin_apply]
    have : heckePrim N ℓ F = fun z : ℍ =>
        ∑ j ∈ Finset.range ℓ, F (heckeMatrix ℓ j • z) + F (heckeDiagMatrix ℓ • z) := by
      funext z; simp [heckePrim, h]
    rw [this]
    exact hasDerivAt_heckeT_primitive hF hℓ τ

theorem aj_lift_sub_dualHeckeRep (ℓ : ℕ) [Fact ℓ.Prime] (τ : ℍ) :
    aj N (lift N ℓ τ) -
        ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ⟨ℓ, Fact.out⟩)
          (ModularCurve.periodAlong N I τ) =
      aj N (lift N ℓ I) := by
  refine LinearMap.ext fun f => ?_
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitive N f
  rw [LinearMap.sub_apply, ModularCurve.dualHeckeRep_apply_apply,
    periodAlong_eq_sub N _ (hasDerivAt_heckePrim N ℓ f hF.1) I τ,
    aj_lift_apply N ℓ f hF.1, aj_lift_apply N ℓ f hF.1]
  simp only [heckePrim]
  split_ifs with h
  · simp only [add_zero, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    ring
  · simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    ring

theorem aj_liftHom_sub_dualHeckeRep (ℓ : ℕ) [Fact ℓ.Prime] (c : ℍ →₀ ℤ) :
    aj N (liftHom N ℓ c) -
        ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ⟨ℓ, Fact.out⟩) (aj N c) =
      (c.sum fun _ n => n) • aj N (lift N ℓ I) := by

  let Φ : (ℍ →₀ ℤ) →+ Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    (aj N).comp (liftHom N ℓ) -
      (ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ⟨ℓ, Fact.out⟩)).toAddMonoidHom.comp (aj N)
  let Ψ : (ℍ →₀ ℤ) →+ Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    (zmultiplesHom _ (aj N (lift N ℓ I))).comp (Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ)
  have hΦΨ : Φ = Ψ := by
    refine Finsupp.addHom_ext fun τ n => ?_
    simp only [Φ, Ψ, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, liftHom_single, map_zsmul,
      aj_single, LinearMap.toAddMonoidHom_coe, Finsupp.liftAddHom_apply_single,
      AddMonoidHom.id_apply, zmultiplesHom_apply, ← smul_sub]
    rw [aj_lift_sub_dualHeckeRep N ℓ τ]
  have h := DFunLike.congr_fun hΦΨ c
  simp only [Φ, Ψ, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    zmultiplesHom_apply, Finsupp.liftAddHom_apply] at h
  rw [h]
  rfl

end AJ

section Curve

variable {N : ℕ} [NeZero N]

scoped instance instIsCurveOver : IsCurveOver ℂ (laurentBaseChange ℂ (modularFunctionFieldFull N)) :=
  ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull ℂ N

theorem deg_eq_one (v : Place ℂ (laurentBaseChange ℂ (modularFunctionFieldFull N))) : v.deg = 1 :=
  IsCurveOver.deg_eq_one_of_isAlgClosed v

theorem degree_mapDomain_pt (D : ModularCurve.ComplexPlaceDictionary N) (c : ℍ →₀ ℤ) :
    Divisor.degree (Finsupp.mapDomain D.pt c) = c.sum fun _ n => n := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, Finsupp.mapDomain_single, ih,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      Divisor.degree_single, deg_eq_one]
    simp

end Curve

section Main

variable {N : ℕ} [NeZero N]

theorem mapDomain_liftHom (D : ModularCurve.ComplexPlaceDictionary N) (ℓ : ℕ) [Fact ℓ.Prime]
    (hα : ModularCurve.HeckeAlphaBarIntegral ℂ N ℓ) (hβ : ModularCurve.HeckeBetaBarIntegral ℂ N ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull (N * ℓ)))]
    (c : ℍ →₀ ℤ) :
    Finsupp.mapDomain D.pt (liftHom N ℓ c) =
      ModularCurve.heckeDivBar hα hβ (Finsupp.mapDomain D.pt c) := by
  classical
  have key : (Finsupp.mapDomain.addMonoidHom D.pt).comp (liftHom N ℓ) =
      (ModularCurve.heckeDivBar hα hβ).comp (Finsupp.mapDomain.addMonoidHom D.pt) := by
    refine Finsupp.addHom_ext fun τ n => ?_
    simp only [AddMonoidHom.comp_apply, Finsupp.mapDomain.addMonoidHom_apply, liftHom_single,
      Finsupp.mapDomain_single]
    rw [Finsupp.mapDomain_smul, ← Finsupp.smul_single_one (D.pt τ) n, map_zsmul,
      ModularCurve.ComplexPlaceDictionary.heckeDivBar_single_pt D ℓ hα hβ τ, lift,
      Finsupp.mapDomain_add, Finsupp.mapDomain_finsetSum]
    congr 2
    · exact Finset.sum_congr rfl fun j _ => Finsupp.mapDomain_single
    · split_ifs
      · exact Finsupp.mapDomain_zero
      · exact Finsupp.mapDomain_single
  simpa using DFunLike.congr_fun key c

theorem main (D : ModularCurve.ComplexPlaceDictionary N) (ℓ : ℕ) [Fact ℓ.Prime]
    (hα : ModularCurve.HeckeAlphaBarIntegral ℂ N ℓ) (hβ : ModularCurve.HeckeBetaBarIntegral ℂ N ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull (N * ℓ)))]
    (c : ℍ →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ c' : ℍ →₀ ℤ,
      Finsupp.mapDomain D.pt c' = ModularCurve.heckeDivBar hα hβ (Finsupp.mapDomain D.pt c) ∧
      (c'.sum fun τ n => n • ModularCurve.periodAlong N I τ) -
          ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ⟨ℓ, Fact.out⟩)
            (c.sum fun τ n => n • ModularCurve.periodAlong N I τ) ∈
        ModularCurve.periodLattice N := by
  refine ⟨liftHom N ℓ c, mapDomain_liftHom D ℓ hα hβ c, ?_⟩
  have hsum : (c.sum fun _ n => n) = 0 := by rw [← degree_mapDomain_pt D c]; exact hdeg
  rw [← aj_apply, ← aj_apply, aj_liftHom_sub_dualHeckeRep N ℓ c, hsum, zero_smul]
  exact Submodule.zero_mem _

end Main

end ModularCurve.HeckeAbelJacobiGlue
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice.ModularCurve.HeckeAbelJacobiGlue"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice.ModularCurve.HeckeAbelJacobiGlue"

theorem solution
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (ℓ : ℕ) [Fact ℓ.Prime]
    (hα : ModularCurve.HeckeAlphaBarIntegral ℂ N ℓ) (hβ : ModularCurve.HeckeBetaBarIntegral ℂ N ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull (N * ℓ)))]
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ c' : UpperHalfPlane →₀ ℤ,
      Finsupp.mapDomain D.pt c' = ModularCurve.heckeDivBar hα hβ (Finsupp.mapDomain D.pt c) ∧
      (c'.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) -
          ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ⟨ℓ, Fact.out⟩)
            (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
        ModularCurve.periodLattice N :=
  ModularCurve.HeckeAbelJacobiGlue.main D ℓ hα hβ c hdeg

end S_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice (solution)
