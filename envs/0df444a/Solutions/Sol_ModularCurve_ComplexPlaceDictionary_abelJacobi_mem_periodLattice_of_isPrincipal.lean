-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.abelJacobi_mem_periodLattice_of_isPrincipal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/385a33ae-eecd-543b-8f43-481c867e3531

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq
import Theorems.Thm_ModularCurve_exists_tendsto_realize_smul_of_forall_ord_eq_zero
import Theorems.Thm_ModularCurve_realize_eq_div
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "realize ComplexPlaceDictionary jq jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange periodAlong period periodLattice ComplexPlaceDictionary.abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq exists_tendsto_realize_smul_of_forall_ord_eq_zero realize_eq_div exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange jqModC_eq_qExpansion_E4_cube_div_discriminant jqModC jqModC_rat map_jqModC"
namespace AbelNecessityAssembly
p2m_open "ModularCurve"

variable {N : ℕ}

abbrev qL {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

structure Pres (N : ℕ) (x : LaurentSeries ℂ) where
  k : ℤ
  g : ModularForm (CongruenceSubgroup.Gamma0 N) k
  h : ModularForm (CongruenceSubgroup.Gamma0 N) k
  h_ne : h ≠ 0
  eq : x * qL h = qL g

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

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

theorem analyticAt_comp_ofComplex {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (τ : ℍ) : AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem eventually_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

theorem eventually_ne_zero_ofComplex {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (f : ℍ → ℂ) (ofComplex z) ≠ 0 :=
  eventually_nhdsNE_coe_iff.mpr (eventually_ne_zero f hf τ)

theorem realize_eventuallyEq {x : LaurentSeries ℂ} (P : Pres N x) (τ : ℍ) :
    (fun z : ℂ => realize N x (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z) / (P.h : ℍ → ℂ) (ofComplex z) := by
  filter_upwards [eventually_ne_zero_ofComplex P.h P.h_ne τ] with z hz
  exact ModularCurve.realize_eq_div N P.g P.h x P.eq (ofComplex z) hz

theorem meromorphicAt_realize {x : LaurentSeries ℂ} (P : Pres N x) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => realize N x (ofComplex z)) (τ : ℂ) :=
  ((analyticAt_comp_ofComplex P.g τ).meromorphicAt.div
    (analyticAt_comp_ofComplex P.h τ).meromorphicAt).congr (realize_eventuallyEq P τ).symm

theorem realize_smul (N : ℕ) (x : LaurentSeries ℂ) (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    realize N x ((γ : SL(2, ℤ)) • τ) = realize N x τ := by
  classical
  by_cases H : ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
        ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
        x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
  · obtain ⟨⟨k, g, h⟩, hτ, heq⟩ := H
    have hh : (h : ℍ → ℂ) ((γ : SL(2, ℤ)) • τ) = denom (γ : SL(2, ℤ)) τ ^ k * (h : ℍ → ℂ) τ :=
      SlashInvariantForm.slash_action_eqn_SL'' h γ.2 τ
    have hg : (g : ℍ → ℂ) ((γ : SL(2, ℤ)) • τ) = denom (γ : SL(2, ℤ)) τ ^ k * (g : ℍ → ℂ) τ :=
      SlashInvariantForm.slash_action_eqn_SL'' g γ.2 τ
    have hd : (denom (γ : SL(2, ℤ)) τ : ℂ) ^ k ≠ 0 := zpow_ne_zero _ (denom_ne_zero _ _)
    have hne : (h : ℍ → ℂ) ((γ : SL(2, ℤ)) • τ) ≠ 0 := by
      rw [hh]; exact mul_ne_zero hd hτ
    rw [ModularCurve.realize_eq_div N g h x heq _ hne, ModularCurve.realize_eq_div N g h x heq _ hτ,
      hg, hh, mul_div_mul_left _ _ hd]
  · have H' : ¬ ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
          ModularForm (CongruenceSubgroup.Gamma0 N) k),
        (p.2.2 : ℍ → ℂ) ((γ : SL(2, ℤ)) • τ) ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
      rintro ⟨p, hτ, heq⟩
      refine H ⟨p, ?_, heq⟩
      intro h0
      apply hτ
      rw [SlashInvariantForm.slash_action_eqn_SL'' p.2.2 γ.2 τ, h0, mul_zero]
    unfold ModularCurve.realize
    rw [dif_neg H, dif_neg H']

section JRegular

theorem Gamma0_le_SL (N : ℕ) :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

def restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ)
    {k : ℤ} (f : F) [ModularFormClass F Γ k] : ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono hle)

@[scoped simp]
theorem coe_restrict {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}
    (hle : Γ' ≤ Γ) {k : ℤ} (f : F) [ModularFormClass F Γ k] :
    ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

variable (N : ℕ)

def G : ModularForm (CongruenceSubgroup.Gamma0 N) 12 :=
  restrict (Gamma0_le_SL N) (ModularForm.mcast (by decide) (ModularForm.E₄.pow 3))

def H : ModularForm (CongruenceSubgroup.Gamma0 N) 12 :=
  restrict (Gamma0_le_SL N) CuspForm.discriminant

theorem coe_G : ((G N : ModularForm _ 12) : ℍ → ℂ) =
    ((ModularForm.E₄.pow 3 : ModularForm 𝒮ℒ (3 * 4)) : ℍ → ℂ) := rfl

theorem coe_H : ((H N : ModularForm _ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem H_apply_ne_zero (z : ℍ) : (H N : ℍ → ℂ) z ≠ 0 := by
  rw [coe_H]
  exact ModularForm.discriminant_ne_zero z

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem H_ne_zero : H N ≠ 0 := by
  intro h
  have := congrArg (fun f : ModularForm (CongruenceSubgroup.Gamma0 N) 12 => (f : ℍ → ℂ) I) h
  exact H_apply_ne_zero N I (by simpa using this)

theorem qL_G : qL (G N) =
    ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by
  have h : qExpansion 1 ((G N : ModularForm _ 12) : ℍ → ℂ) =
      (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
    rw [coe_G, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [qL, h, PowerSeries.coe_pow]

theorem qL_H : qL (H N) =
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  rfl

theorem coeffEmb_jq_eq : coeffEmb ℂ jq = jqModC ℂ := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ ℂ)

theorem coeffEmb_jq_mul_qL_H : coeffEmb ℂ jq * qL (H N) = qL (G N) := by
  rw [coeffEmb_jq_eq, jqModC_eq_qExpansion_E4_cube_div_discriminant, qL_G, ← qL_H N]
  exact div_mul_cancel₀ _ (qL_ne_zero N (H N) (H_ne_zero N))

theorem realize_coeffEmb_jq (z : ℍ) :
    realize N (coeffEmb ℂ jq) z = (G N : ℍ → ℂ) z / (H N : ℍ → ℂ) z :=
  ModularCurve.realize_eq_div N (G N) (H N) (coeffEmb ℂ jq) (coeffEmb_jq_mul_qL_H N) z
    (H_apply_ne_zero N z)

theorem isBoundedUnder_realize_coeffEmb_jq (τ : ℍ) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realize N (coeffEmb ℂ jq) z‖) := by
  have hcont : Continuous (fun z : ℍ => (G N : ℍ → ℂ) z / (H N : ℍ → ℂ) z) :=
    (ModularFormClass.holo (G N)).continuous.div (ModularFormClass.holo (H N)).continuous
      (H_apply_ne_zero N)
  have hbd : IsBoundedUnder (· ≤ ·) (𝓝 τ)
      (fun z : ℍ => ‖(G N : ℍ → ℂ) z / (H N : ℍ → ℂ) z‖) :=
    (hcont.continuousAt.norm.tendsto).isBoundedUnder_le
  have hfun : (fun z : ℍ => ‖realize N (coeffEmb ℂ jq) z‖) =
      fun z : ℍ => ‖(G N : ℍ → ℂ) z / (H N : ℍ → ℂ) z‖ :=
    funext fun z => by rw [realize_coeffEmb_jq]
  rw [hfun]
  exact hbd.mono nhdsWithin_le_nhds

def jX (N : ℕ) [NeZero N] : laurentBaseChange ℂ (modularFunctionFieldFull N) :=
  ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (modularFunctionField_le_full N (jq_mem N))⟩

theorem jX_mem_pt [NeZero N] (D : ComplexPlaceDictionary N) (τ : ℍ) :
    jX N ∈ (D.pt τ).toValuationSubring :=
  (D.mem_pt_iff τ (jX N)).mpr (isBoundedUnder_realize_coeffEmb_jq N τ)

end JRegular

theorem ord_eq_zero_of_cuspidal [NeZero N] (D : ComplexPlaceDictionary N) (c : ℍ →₀ ℤ)
    {x : laurentBaseChange ℂ (modularFunctionFieldFull N)}
    (hx : ∀ v, Finsupp.mapDomain D.pt c v = v.ord x)
    (v : AlgebraicCurve.Place ℂ (laurentBaseChange ℂ (modularFunctionFieldFull N)))
    (hv : jX N ∉ v.toValuationSubring) : v.ord x = 0 := by
  have hvr : v ∉ Set.range D.pt := by
    rintro ⟨τ, rfl⟩
    exact hv (jX_mem_pt N D τ)
  rw [← hx v, Finsupp.mapDomain_notin_range _ _ hvr]

end ModularCurve.AbelNecessityAssembly
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal.ModularCurve.AbelNecessityAssembly"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal.ModularCurve.AbelNecessityAssembly"

open UpperHalfPlane _root_.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal.ModularCurve ModularCurve.AbelNecessityAssembly in
open scoped MatrixGroups Topology in
theorem solution
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (c : UpperHalfPlane →₀ ℤ)
    (hc : AlgebraicCurve.Divisor.IsPrincipal (Finsupp.mapDomain D.pt c)) :
    (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
      ModularCurve.periodLattice N := by
  obtain ⟨x, hx0, hx⟩ := hc

  obtain ⟨k, g, h, hh, heq⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N
      (x : LaurentSeries ℂ) x.2
  let P : Pres N (x : LaurentSeries ℂ) := ⟨k, g, h, hh, heq⟩
  refine ModularCurve.ComplexPlaceDictionary.abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq
    D c (ModularCurve.realize N (x : LaurentSeries ℂ)) (fun τ => meromorphicAt_realize P τ)
    (fun γ hγ τ => realize_smul N (x : LaurentSeries ℂ) ⟨γ, hγ⟩ τ) (fun σ => ?_) (fun τ => ?_)
  ·
    exact ModularCurve.exists_tendsto_realize_smul_of_forall_ord_eq_zero N x hx0
      (fun v hv => ord_eq_zero_of_cuspidal D c hx v hv) σ
  ·
    rw [D.meromorphicOrderAt_realize τ x hx0, ← hx (D.pt τ)]

end S_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal (solution)
