-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9e859c23-596b-5eca-8dab-1cdb7047f913

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer_gammaH
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "UpperHalfPlane Filter ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal.ModularCurve"
open scoped MatrixGroups Topology ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf realizeOf_of_not ComplexPlaceDictionaryOf coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange translation_mem_GammaH Gamma1_le_GammaH xHFunctionField intFormRatiosC_subset periodAlongOf periodLatticeOf jqModC map_jqModC abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer_gammaH ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH realizeOf_eq_div exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC jqModC_eq_qExpansion_E4_cube_div_discriminant jqModC_mem_intFormRatiosC"
namespace AbelNecessityHAssembly
p2m_open "ModularCurve"

variable {Γ : Subgroup SL(2, ℤ)}

abbrev qL {k : ℤ} (f : ModularForm Γ k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm Γ k) : (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem qL_ne_zero (hT : ModularGroup.T ∈ Γ) {k : ℤ} (f : ModularForm Γ k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods hT)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

theorem eventually_nhdsNE_coe_iff {p : ℍ → Prop} {τ : ℍ} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

theorem analyticAt_comp_ofComplex {k : ℤ} (f : ModularForm Γ k) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem eventually_ne_zero {k : ℤ} (f : ModularForm Γ k) (hf : f ≠ 0) (τ : ℍ) :
    ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

theorem eventually_ne_zero_ofComplex {k : ℤ} (f : ModularForm Γ k) (hf : f ≠ 0) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), (f : ℍ → ℂ) (ofComplex z) ≠ 0 :=
  eventually_nhdsNE_coe_iff.mpr (eventually_ne_zero f hf τ)

theorem realizeOf_eventuallyEq (hT : ModularGroup.T ∈ Γ) {x : LaurentSeries ℂ} {k : ℤ}
    (g h : ModularForm Γ k) (hh : h ≠ 0) (heq : x * qL h = qL g) (τ : ℍ) :
    (fun z : ℂ => realizeOf Γ x (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) := by
  filter_upwards [eventually_ne_zero_ofComplex h hh τ] with z hz
  exact ModularCurve.realizeOf_eq_div Γ hT g h x heq (ofComplex z) hz

theorem meromorphicAt_realizeOf (hT : ModularGroup.T ∈ Γ) {x : LaurentSeries ℂ} {k : ℤ}
    (g h : ModularForm Γ k) (hh : h ≠ 0) (heq : x * qL h = qL g) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => realizeOf Γ x (ofComplex z)) (τ : ℂ) :=
  ((analyticAt_comp_ofComplex g τ).meromorphicAt.div
    (analyticAt_comp_ofComplex h τ).meromorphicAt).congr (realizeOf_eventuallyEq hT g h hh heq τ).symm

theorem realizeOf_smul (hT : ModularGroup.T ∈ Γ) (x : LaurentSeries ℂ) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ)
    (τ : ℍ) : realizeOf Γ x (γ • τ) = realizeOf Γ x τ := by
  classical
  by_cases H : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
      (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
        x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
  · obtain ⟨⟨k, g, h⟩, hτ, heq⟩ := H
    have hh : (h : ℍ → ℂ) (γ • τ) = denom γ τ ^ k * (h : ℍ → ℂ) τ :=
      SlashInvariantForm.slash_action_eqn_SL'' h hγ τ
    have hg : (g : ℍ → ℂ) (γ • τ) = denom γ τ ^ k * (g : ℍ → ℂ) τ :=
      SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
    have hd : (denom γ τ : ℂ) ^ k ≠ 0 := zpow_ne_zero _ (denom_ne_zero _ _)
    have hne : (h : ℍ → ℂ) (γ • τ) ≠ 0 := by
      rw [hh]; exact mul_ne_zero hd hτ
    rw [ModularCurve.realizeOf_eq_div Γ hT g h x heq _ hne,
      ModularCurve.realizeOf_eq_div Γ hT g h x heq _ hτ, hg, hh, mul_div_mul_left _ _ hd]
  · have H' : ¬ ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : ℍ → ℂ) (γ • τ) ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
      rintro ⟨p, hτ, heq⟩
      refine H ⟨p, ?_, heq⟩
      intro h0
      apply hτ
      rw [SlashInvariantForm.slash_action_eqn_SL'' p.2.2 hγ τ, h0, mul_zero]
    rw [ModularCurve.realizeOf_of_not Γ x _ H', ModularCurve.realizeOf_of_not Γ x _ H]

section JRegular

variable (Γ)

theorem le_SL : ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

variable {Γ}

def restrict {F : Type*} [FunLike F ℍ ℂ] {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (hle : Γ₂ ≤ Γ₁)
    {k : ℤ} (f : F) [ModularFormClass F Γ₁ k] : ModularForm Γ₂ k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono hle)

@[scoped simp]
theorem coe_restrict {F : Type*} [FunLike F ℍ ℂ] {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)}
    (hle : Γ₂ ≤ Γ₁) {k : ℤ} (f : F) [ModularFormClass F Γ₁ k] :
    ((restrict hle f : ModularForm Γ₂ k) : ℍ → ℂ) = f := rfl

variable (Γ)

def G : ModularForm Γ 12 :=
  restrict (le_SL Γ) (ModularForm.mcast (by decide) (ModularForm.E₄.pow 3))

def HΔ : ModularForm Γ 12 :=
  restrict (le_SL Γ) CuspForm.discriminant

theorem coe_G : ((G Γ : ModularForm _ 12) : ℍ → ℂ) =
    ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) := rfl

theorem coe_HΔ : ((HΔ Γ : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem HΔ_apply_ne_zero (z : ℍ) : (HΔ Γ : ℍ → ℂ) z ≠ 0 := by
  rw [coe_HΔ]
  exact ModularForm.discriminant_ne_zero z

theorem HΔ_ne_zero : HΔ Γ ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm Γ 12 => (f : ℍ → ℂ) I) h
  exact HΔ_apply_ne_zero Γ I (by simpa using this)

theorem qL_G : qL (G Γ) =
    ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by
  have h : qExpansion 1 ((G Γ : ModularForm _ 12) : ℍ → ℂ) =
      (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
    rw [coe_G, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [qL, h, PowerSeries.coe_pow]

theorem qL_HΔ : qL (HΔ Γ) =
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  rfl

theorem jqModC_mul_qL_HΔ (hT : ModularGroup.T ∈ Γ) : jqModC ℂ * qL (HΔ Γ) = qL (G Γ) := by
  rw [jqModC_eq_qExpansion_E4_cube_div_discriminant, qL_G Γ, ← qL_HΔ Γ]
  exact div_mul_cancel₀ _ (qL_ne_zero hT (HΔ Γ) (HΔ_ne_zero Γ))

theorem realizeOf_jqModC (hT : ModularGroup.T ∈ Γ) (z : ℍ) :
    realizeOf Γ (jqModC ℂ) z = (G Γ : ℍ → ℂ) z / (HΔ Γ : ℍ → ℂ) z :=
  ModularCurve.realizeOf_eq_div Γ hT (G Γ) (HΔ Γ) (jqModC ℂ) (jqModC_mul_qL_HΔ Γ hT) z
    (HΔ_apply_ne_zero Γ z)

theorem isBoundedUnder_realizeOf_jqModC (hT : ModularGroup.T ∈ Γ) (τ : ℍ) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realizeOf Γ (jqModC ℂ) z‖) := by
  have hcont : Continuous (fun z : ℍ => (G Γ : ℍ → ℂ) z / (HΔ Γ : ℍ → ℂ) z) :=
    (ModularFormClass.holo (G Γ)).continuous.div (ModularFormClass.holo (HΔ Γ)).continuous
      (HΔ_apply_ne_zero Γ)
  have hbd : IsBoundedUnder (· ≤ ·) (𝓝 τ)
      (fun z : ℍ => ‖(G Γ : ℍ → ℂ) z / (HΔ Γ : ℍ → ℂ) z‖) :=
    (hcont.continuousAt.norm.tendsto).isBoundedUnder_le
  have hfun : (fun z : ℍ => ‖realizeOf Γ (jqModC ℂ) z‖) =
      fun z : ℍ => ‖(G Γ : ℍ → ℂ) z / (HΔ Γ : ℍ → ℂ) z‖ :=
    funext fun z => by rw [realizeOf_jqModC Γ hT]
  rw [hfun]
  exact hbd.mono nhdsWithin_le_nhds

end JRegular

section GammaH

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "𝔽" => (laurentBaseChange ℂ (xHFunctionField M H))
local notation "ΓH" => (CohCarrier.GammaH M H)

def jH : laurentBaseChange ℂ (xHFunctionField M H) :=
  ⟨coeffEmb ℂ (jqModC ℚ),
    coeffEmb_mem_laurentBaseChange ℂ
      (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H) (jqModC_mem_intFormRatiosC ℚ (CohCarrier.GammaH M H)))⟩

theorem coe_jH : ((jH M H : 𝔽) : LaurentSeries ℂ) = jqModC ℂ := by
  show coeffEmb ℂ (jqModC ℚ) = _
  exact map_jqModC (algebraMap ℚ ℂ)

variable {M H}

theorem jH_mem_pt (D : ComplexPlaceDictionaryOf ΓH (xHFunctionField M H)) (τ : ℍ) :
    jH M H ∈ (D.pt τ).toValuationSubring := by
  rw [D.mem_pt_iff τ (jH M H), coe_jH]
  exact isBoundedUnder_realizeOf_jqModC ΓH (translation_mem_GammaH M H) τ

theorem ord_eq_zero_of_cuspidal (D : ComplexPlaceDictionaryOf ΓH (xHFunctionField M H)) (c : ℍ →₀ ℤ)
    {x : 𝔽} (hx : ∀ v, Finsupp.mapDomain D.pt c v = v.ord x)
    (v : AlgebraicCurve.Place ℂ 𝔽) (hv : jH M H ∉ v.toValuationSubring) : v.ord x = 0 := by
  have hvr : v ∉ Set.range D.pt := by
    rintro ⟨τ, rfl⟩
    exact hv (jH_mem_pt D τ)
  rw [← hx v, Finsupp.mapDomain_notin_range _ _ hvr]

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (f : α → β) (c : α →₀ ℤ) (a : α) :
    Finsupp.mapDomain f c (f a) = c.sum fun σ n => if f σ = f a then n else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finsupp.sum_congr fun σ _ => ?_
  rw [Finsupp.single_apply]

theorem fibre_iff (D : ComplexPlaceDictionaryOf ΓH (xHFunctionField M H)) (σ τ : ℍ) :
    D.pt σ = D.pt τ ↔
      Quotient.mk (MulAction.orbitRel ΓH ℍ) σ = Quotient.mk (MulAction.orbitRel ΓH ℍ) τ := by
  rw [ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH M H D σ τ, Quotient.eq, MulAction.orbitRel_apply,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, hγ, hγσ⟩
    refine ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    rw [← hγσ]
    show ((⟨γ, hγ⟩⁻¹ : ΓH) : SL(2, ℤ)) • (γ • σ) = σ
    rw [Subgroup.coe_inv, inv_smul_smul]
  · rintro ⟨γ, hγ⟩
    refine ⟨((γ⁻¹ : ΓH) : SL(2, ℤ)), (γ⁻¹).2, ?_⟩
    rw [← hγ]
    show ((γ⁻¹ : ΓH) : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • τ) = τ
    rw [Subgroup.coe_inv, inv_smul_smul]

theorem pushforward_eq (D : ComplexPlaceDictionaryOf ΓH (xHFunctionField M H)) (c : ℍ →₀ ℤ) (τ : ℍ) :
    Finsupp.mapDomain D.pt c (D.pt τ) =
      Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel ΓH ℍ)) c
        (Quotient.mk (MulAction.orbitRel ΓH ℍ) τ) := by
  classical
  rw [mapDomain_apply_eq_sum, mapDomain_apply_eq_sum]
  refine Finsupp.sum_congr fun σ _ => ?_
  exact if_congr (fibre_iff D σ τ) rfl rfl

theorem ramification_eq (D : ComplexPlaceDictionaryOf ΓH (xHFunctionField M H)) (τ : ℍ) :
    D.ramification τ =
      Nat.card (MulAction.stabilizer
        (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) / 2 := by
  rw [← ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer_gammaH M H D τ,
    Nat.mul_div_cancel_left _ (by norm_num)]

end GammaH

end ModularCurve.AbelNecessityHAssembly
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal.ModularCurve.AbelNecessityHAssembly"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal.ModularCurve.AbelNecessityHAssembly"

open UpperHalfPlane _root_.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal.ModularCurve ModularCurve.AbelNecessityHAssembly in
open scoped MatrixGroups Topology in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hc : AlgebraicCurve.Divisor.IsPrincipal (Finsupp.mapDomain D.pt c)) :
    (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) := by
  obtain ⟨x, hx0, hx⟩ := hc
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

  obtain ⟨k, g, h, hh, heq⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
      (CohCarrier.GammaH M H) hT (x : LaurentSeries ℂ) x.2
  refine ModularCurve.abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer
    (CohCarrier.GammaH M H) c (ModularCurve.realizeOf (CohCarrier.GammaH M H) (x : LaurentSeries ℂ))
    (fun τ => meromorphicAt_realizeOf hT g h hh heq τ)
    (fun γ hγ τ => realizeOf_smul hT (x : LaurentSeries ℂ) hγ τ) (fun σ => ?_) (fun τ => ?_)
  ·
    exact ModularCurve.exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero (CohCarrier.GammaH M H) hT
      (xHFunctionField M H) rfl x hx0 (jH M H) (coe_jH M H)
      (fun v hv => ord_eq_zero_of_cuspidal D c hx v hv) σ
  ·
    rw [D.meromorphicOrderAt_realizeOf τ x hx0, ← hx (D.pt τ), ramification_eq D τ, pushforward_eq D c τ]

end S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_abelJacobi_mem_periodLatticeOf_gammaH_of_isPrincipal (solution)
