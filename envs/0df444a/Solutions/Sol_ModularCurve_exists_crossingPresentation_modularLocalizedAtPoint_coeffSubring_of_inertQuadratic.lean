-- Prove2me | solution 1 for ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8cfea52f-f338-57a0-b559-c9d63d15b4f4

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_span_uniformizer_pair_eq_branches_or_swap_of_maximalIdeal_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic.ModularCurve.NodeLocalized MvPolynomial"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.integralCoeffs CharPReduction.constSeries CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.constSeries_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs algebraMap_laurentSeries_eq_single ssJSet jWidth jWidth_pos NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring NodeLocalized.span_uniformizer_pair_eq_branches_or_swap_of_maximalIdeal_eq_span"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict pointEval_eq_zero_of_modularEval_eq_zero coeffSubring_eq_or_isDiscreteValuationRing isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring span_uniformizer_pair_eq_branches_or_swap_of_maximalIdeal_eq_span"
namespace InertDescent
p2m_open "ModularCurve.NodeLocalized ModularCurve"

theorem mem_span_singleton_of_mul_mem {R : Type*} [CommRing R] [IsDomain R] {π G H w : R} (hw : IsUnit w)
    {E : ℕ} (hGH : G * H = π ^ E * w) (hQ : (Ideal.span {π, H}).IsPrime) (hG : G ∉ Ideal.span {π, H})
    {s f : R} (hs : s ∉ Ideal.span {π, H}) (hsf : s * f ∈ Ideal.span {H}) : f ∈ Ideal.span {H} := by
  have hπE : π ^ E ∈ Ideal.span ({H} : Set R) := by
    obtain ⟨u, rfl⟩ := hw
    refine Ideal.mem_span_singleton'.mpr ⟨G * ↑u⁻¹, ?_⟩
    calc G * ↑u⁻¹ * H = G * H * ↑u⁻¹ := by ring
      _ = π ^ E * ↑u * ↑u⁻¹ := by rw [hGH]
      _ = π ^ E := by rw [mul_assoc, Units.mul_inv, mul_one]
  by_cases hπ : π = 0
  · subst hπ
    rcases Nat.eq_zero_or_pos E with hE | hE
    ·
      rw [hE, pow_zero] at hπE
      have : Ideal.span ({H} : Set R) = ⊤ := (Ideal.eq_top_iff_one _).mpr hπE
      rw [this]; exact Submodule.mem_top
    · have h0 : G * H = 0 := by rw [hGH, zero_pow hE.ne', zero_mul]
      rcases mul_eq_zero.mp h0 with hG0 | hH0
      · exact absurd (by rw [hG0]; exact zero_mem _) hG
      · subst hH0
        have hs0 : s ≠ 0 := fun h => hs (by rw [h]; exact zero_mem _)
        have hsf0 : s * f = 0 := by
          rw [Ideal.span_singleton_eq_bot.mpr rfl] at hsf
          exact hsf
        rcases mul_eq_zero.mp hsf0 with h | h
        · exact absurd h hs0
        · rw [h]; exact zero_mem _

  have key : ∀ n, n ≤ E → ∃ a b, f = H * a + π ^ n * b := by
    intro n
    induction n with
    | zero => intro _; exact ⟨0, f, by ring⟩
    | succ n ih =>
      intro hn
      obtain ⟨a, b, hab⟩ := ih (Nat.le_of_succ_le hn)
      have h1 : s * (π ^ n * b) ∈ Ideal.span ({H} : Set R) := by
        have : s * (π ^ n * b) = s * f - H * (s * a) := by rw [hab]; ring
        rw [this]
        exact sub_mem hsf (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self H))
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
      have hEn : E = n + (E - n) := by omega
      have h2 : π ^ n * (s * b * G) = π ^ n * (π ^ (E - n) * w * c) := by
        calc π ^ n * (s * b * G) = (s * (π ^ n * b)) * G := by ring
          _ = c * H * G := by rw [hc]
          _ = c * (G * H) := by ring
          _ = c * (π ^ E * w) := by rw [hGH]
          _ = c * (π ^ (n + (E - n)) * w) := by rw [← hEn]
          _ = π ^ n * (π ^ (E - n) * w * c) := by rw [pow_add]; ring
      have h3 : s * b * G = π ^ (E - n) * w * c := mul_left_cancel₀ (pow_ne_zero n hπ) h2
      have h4 : s * b * G ∈ Ideal.span ({π, H} : Set R) := by
        rw [h3]
        obtain ⟨m, hm⟩ : ∃ m, E - n = m + 1 := ⟨E - n - 1, by omega⟩
        rw [hm, pow_succ]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))))
      have h5 : b ∈ Ideal.span ({π, H} : Set R) := by
        rcases hQ.mem_or_mem h4 with h | h
        · rcases hQ.mem_or_mem h with h' | h'
          · exact absurd h' hs
          · exact h'
        · exact absurd h hG
      obtain ⟨b₁, b₂, hb⟩ := Ideal.mem_span_pair.mp h5
      refine ⟨a + π ^ n * b₂, b₁, ?_⟩
      rw [hab, ← hb]; ring
  obtain ⟨a, b, hab⟩ := key E le_rfl
  rw [hab]
  exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self H)) (Ideal.mul_mem_right _ _ hπE)

theorem isUnit_or_isUnit_of_eq_mul_add {R : Type*} [CommRing R] [IsLocalRing R] [IsDomain R] {x ζ u₀ u₁ : R}
    (hx : x ≠ 0) (h : x = x * u₀ + ζ * (x * u₁)) : IsUnit u₀ ∨ IsUnit u₁ := by
  have h1 : x * (u₀ + ζ * u₁) = x * 1 := by rw [mul_one]; nth_rw 2 [h]; ring
  have h2 : u₀ + ζ * u₁ = 1 := mul_left_cancel₀ hx h1
  by_contra hcon
  push Not at hcon
  have hm0 : u₀ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hcon.1
  have hm1 : ζ * u₁ ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hcon.2)
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := h2 ▸ add_mem hm0 hm1
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)

theorem pow_mem_span_pow_of_mem_span {S : Type*} [CommRing S] {π G y : S} (hy : y ∈ Ideal.span {π, G}) (n : ℕ) :
    y ^ n ∈ Ideal.span {π ^ n, G} := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Ideal.subset_span (Set.mem_insert _ _)
  | succ n ih =>
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hy
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp ih
    have : y ^ (n + 1) = (c * a) * π ^ (n + 1) + (c * π ^ n * b + d * (a * π + b * G)) * G := by
      calc y ^ (n + 1) = y ^ n * y := pow_succ y n
        _ = (c * π ^ n + d * G) * (a * π + b * G) := by rw [hcd, hab]
        _ = (c * a) * π ^ (n + 1) + (c * π ^ n * b + d * (a * π + b * G)) * G := by ring
    rw [this]
    exact Ideal.mem_span_pair.mpr ⟨_, _, rfl⟩

theorem span_pair_eq_of_eq_mul_unit {S : Type*} [CommRing S] (p X Y : S) (u : Sˣ) (hXY : Y = X * u) :
    Ideal.span {p, Y} = Ideal.span {p, X} := by
  apply le_antisymm
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, SetLike.mem_coe]
    refine ⟨Ideal.subset_span (Set.mem_insert _ _), ?_⟩
    rw [hXY]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, SetLike.mem_coe]
    refine ⟨Ideal.subset_span (Set.mem_insert _ _), ?_⟩
    have : X = Y * ↑u⁻¹ := by rw [hXY, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem core {R S : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing S] [IsDomain S] [IsLocalRing S]
    (φ : R →+* S) (ζ : S)
    (decomp : ∀ f : S, ∃ f₀ f₁ : R, f = φ f₀ + ζ * φ f₁)
    (uniq : ∀ f₀ f₁ g₀ g₁ : R, φ f₀ + ζ * φ f₁ = φ g₀ + ζ * φ g₁ → f₀ = g₀ ∧ f₁ = g₁)
    (π g h : R) (hπ : π ≠ 0) (E : ℕ) (G H w : S) (hw : IsUnit w)
    (hGH : G * H = φ π ^ E * w) (hmax : IsLocalRing.maximalIdeal S = Ideal.span {φ π, G, H})
    (hP : (Ideal.span {φ π, G}).IsPrime) (hQ : (Ideal.span {φ π, H}).IsPrime)
    (hHn : H ∉ Ideal.span {φ π, G}) (hGn : G ∉ Ideal.span {φ π, H})
    (hpinG : Ideal.span {φ π, G} = Ideal.span {φ π, φ g}) (hpinH : Ideal.span {φ π, H} = Ideal.span {φ π, φ h}) :
    ∃ G₀ H₀ w₀ : R, IsUnit w₀ ∧ G₀ * H₀ = π ^ E * w₀ ∧ IsLocalRing.maximalIdeal R = Ideal.span {π, G₀, H₀} ∧
      Ideal.span {φ π, φ G₀} = Ideal.span {φ π, G} ∧ Ideal.span {φ π, φ H₀} = Ideal.span {φ π, H} := by

  have hφinj : Function.Injective φ := by
    intro r s hrs
    exact (uniq r 0 s 0 (by rw [hrs])).1
  have hφ0 : φ π ≠ 0 := fun h0 => hπ (hφinj (by rw [h0, map_zero]))
  have unit_desc : ∀ r : R, IsUnit (φ r) → IsUnit r := by
    intro r hr
    obtain ⟨v, hv⟩ := hr.exists_right_inv
    obtain ⟨v₀, v₁, hv01⟩ := decomp v
    have h1 : φ (r * v₀) + ζ * φ (r * v₁) = φ 1 + ζ * φ 0 := by
      rw [map_mul, map_mul, map_one, map_zero, mul_zero, add_zero, ← hv, hv01]; ring
    exact isUnit_iff_exists_inv.mpr ⟨v₀, (uniq _ _ _ _ h1).1⟩
  have mem01 : ∀ (p X : S), p ∈ Ideal.span ({p, X} : Set S) := fun p X => Ideal.subset_span (Set.mem_insert _ _)
  have mem02 : ∀ (p X : S), X ∈ Ideal.span ({p, X} : Set S) := fun p X =>
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

  have hg_mem : φ g ∈ Ideal.span {φ π, G} := by rw [hpinG]; exact mem02 _ _
  have hh_mem : φ h ∈ Ideal.span {φ π, H} := by rw [hpinH]; exact mem02 _ _
  have hg_not : φ g ∉ Ideal.span {φ π, H} := by
    intro hmem
    apply hGn
    have hle : Ideal.span {φ π, G} ≤ Ideal.span {φ π, H} := by
      rw [hpinG, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, SetLike.mem_coe]
      exact ⟨mem01 _ _, hmem⟩
    exact hle (mem02 _ _)
  have hh_not : φ h ∉ Ideal.span {φ π, G} := by
    intro hmem
    apply hHn
    have hle : Ideal.span {φ π, H} ≤ Ideal.span {φ π, G} := by
      rw [hpinH, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, SetLike.mem_coe]
      exact ⟨mem01 _ _, hmem⟩
    exact hle (mem02 _ _)
  have hHG : H * G = φ π ^ E * w := by rw [mul_comm]; exact hGH

  have gen_desc : ∀ (X Y : S) (t : R), (Ideal.span {φ π, X}).IsPrime → Y ∉ Ideal.span {φ π, X} →
      Y * X = φ π ^ E * w → φ t ∉ Ideal.span {φ π, X} → φ t ∈ Ideal.span {φ π, Y} →
      ∃ (X₀ : R) (u : Sˣ), φ X₀ = X * u := by
    intro X Y t hXp hYn hYX ht_not ht_mem
    have hπE_X : φ π ^ E ∈ Ideal.span ({X} : Set S) := by
      obtain ⟨u, rfl⟩ := hw
      refine Ideal.mem_span_singleton'.mpr ⟨Y * ↑u⁻¹, ?_⟩
      calc Y * ↑u⁻¹ * X = Y * X * ↑u⁻¹ := by ring
        _ = φ π ^ E * ↑u * ↑u⁻¹ := by rw [hYX]
        _ = φ π ^ E := by rw [mul_assoc, Units.mul_inv, mul_one]
    have h1 : (φ t) ^ E ∈ Ideal.span {φ π ^ E, Y} := pow_mem_span_pow_of_mem_span ht_mem E
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp h1
    have h2 : (φ t) ^ E * X = φ π ^ E * (c * X + d * w) := by
      rw [← hcd]
      calc (c * φ π ^ E + d * Y) * X = c * φ π ^ E * X + d * (Y * X) := by ring
        _ = c * φ π ^ E * X + d * (φ π ^ E * w) := by rw [hYX]
        _ = φ π ^ E * (c * X + d * w) := by ring
    obtain ⟨x₀, x₁, hx01⟩ := decomp X
    obtain ⟨m₀, m₁, hm01⟩ := decomp (c * X + d * w)
    rw [hm01] at h2
    rw [hx01] at h2
    have h3 : φ (t ^ E * x₀) + ζ * φ (t ^ E * x₁) = φ (π ^ E * m₀) + ζ * φ (π ^ E * m₁) := by
      simp only [map_mul, map_pow]
      linear_combination h2
    obtain ⟨e0, e1⟩ := uniq _ _ _ _ h3
    have hsE : (φ t) ^ E ∉ Ideal.span {φ π, X} := fun hm => ht_not (hXp.mem_of_pow_mem E hm)
    have hXi : ∀ xi mi : R, t ^ E * xi = π ^ E * mi → φ xi ∈ Ideal.span {X} := by
      intro xi mi hxm
      refine mem_span_singleton_of_mul_mem hw hYX hXp hYn hsE ?_
      rw [← map_pow, ← map_mul, hxm, map_mul, map_pow]
      exact Ideal.mul_mem_right _ _ hπE_X
    obtain ⟨u₀, hu₀⟩ := Ideal.mem_span_singleton'.mp (hXi x₀ m₀ e0)
    obtain ⟨u₁, hu₁⟩ := Ideal.mem_span_singleton'.mp (hXi x₁ m₁ e1)
    have hX0 : X ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hYX
      exact (mul_ne_zero (pow_ne_zero E hφ0) hw.ne_zero) hYX.symm
    have hdec : X = X * u₀ + ζ * (X * u₁) := by
      rw [mul_comm X u₀, mul_comm X u₁, hu₀, hu₁]; exact hx01
    rcases isUnit_or_isUnit_of_eq_mul_add hX0 hdec with hu | hu
    · exact ⟨x₀, hu.unit, by rw [IsUnit.unit_spec, ← hu₀, mul_comm]⟩
    · exact ⟨x₁, hu.unit, by rw [IsUnit.unit_spec, ← hu₁, mul_comm]⟩
  obtain ⟨H₀, uH, hH₀⟩ := gen_desc H G g hQ hGn hGH hg_not hg_mem
  obtain ⟨G₀, uG, hG₀⟩ := gen_desc G H h hP hHn hHG hh_not hh_mem

  obtain ⟨w₀, w₁, hw01⟩ := decomp (w * ↑uG * ↑uH)
  have h4 : φ (G₀ * H₀) + ζ * φ 0 = φ (π ^ E * w₀) + ζ * φ (π ^ E * w₁) := by
    have : φ (G₀ * H₀) = φ π ^ E * (w * ↑uG * ↑uH) := by
      rw [map_mul, hG₀, hH₀]
      calc G * ↑uG * (H * ↑uH) = G * H * ↑uG * ↑uH := by ring
        _ = φ π ^ E * w * ↑uG * ↑uH := by rw [hGH]
        _ = φ π ^ E * (w * ↑uG * ↑uH) := by ring
    rw [this, hw01, map_zero, mul_zero, add_zero, map_mul, map_mul, map_pow]
    ring
  obtain ⟨hGH₀, hw1⟩ := uniq _ _ _ _ h4
  have hw1' : w₁ = 0 := by
    rcases mul_eq_zero.mp hw1.symm with h0 | h0
    · exact absurd (pow_eq_zero_iff'.mp h0).1 hπ
    · exact h0
  have hw₀S : φ w₀ = w * ↑uG * ↑uH := by
    rw [hw01, hw1', map_zero, mul_zero, add_zero]
  have hw₀ : IsUnit w₀ := unit_desc w₀ (by
    rw [hw₀S]; exact (hw.mul (Units.isUnit _)).mul (Units.isUnit _))

  have hmaxR : IsLocalRing.maximalIdeal R = Ideal.span {π, G₀, H₀} := by
    apply le_antisymm
    · intro r hr
      have hr' : φ r ∈ IsLocalRing.maximalIdeal S := by
        rw [IsLocalRing.mem_maximalIdeal] at hr ⊢
        exact fun hu => hr (unit_desc r hu)
      rw [hmax] at hr'
      obtain ⟨a₁, z₁, hz₁, hr1⟩ := Ideal.mem_span_insert.mp hr'
      obtain ⟨a₂, z₂, hz₂, hr2⟩ := Ideal.mem_span_insert.mp hz₁
      obtain ⟨a₃, hr3⟩ := Ideal.mem_span_singleton'.mp hz₂
      obtain ⟨b₁, c₁, hbc₁⟩ := decomp a₁
      obtain ⟨b₂, c₂, hbc₂⟩ := decomp (a₂ * ↑uG⁻¹)
      obtain ⟨b₃, c₃, hbc₃⟩ := decomp (a₃ * ↑uH⁻¹)
      have hGe : G = φ G₀ * ↑uG⁻¹ := by rw [hG₀, mul_assoc, Units.mul_inv, mul_one]
      have hHe : H = φ H₀ * ↑uH⁻¹ := by rw [hH₀, mul_assoc, Units.mul_inv, mul_one]
      have h5 : φ r + ζ * φ 0 =
          φ (b₁ * π + b₂ * G₀ + b₃ * H₀) + ζ * φ (c₁ * π + c₂ * G₀ + c₃ * H₀) := by
        have e : φ r = a₁ * φ π + (a₂ * ↑uG⁻¹) * φ G₀ + (a₃ * ↑uH⁻¹) * φ H₀ := by
          rw [hr1, hr2, ← hr3, hGe, hHe]; ring
        rw [map_zero, mul_zero, add_zero, e, hbc₁, hbc₂, hbc₃]
        simp only [map_add, map_mul]
        ring
      have h6 := (uniq _ _ _ _ h5).1
      rw [h6]
      refine add_mem (add_mem ?_ ?_) ?_
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    · have hS : ∀ y : S, y ∈ Ideal.span ({φ π, G, H} : Set S) → ¬ IsUnit y := by
        intro y hy
        rw [← hmax] at hy
        exact (IsLocalRing.mem_maximalIdeal _).mp hy
      rw [Ideal.span_le, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        SetLike.mem_coe, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal]
      refine ⟨fun hu => ?_, fun hu => ?_, fun hu => ?_⟩
      · exact hS (φ π) (Ideal.subset_span (Set.mem_insert _ _)) (hu.map φ)
      · refine hS (φ G₀) ?_ (hu.map φ)
        rw [hG₀]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      · refine hS (φ H₀) ?_ (hu.map φ)
        rw [hH₀]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  exact ⟨G₀, H₀, w₀, hw₀, hGH₀, hmaxR, span_pair_eq_of_eq_mul_unit _ _ _ uG hG₀,
    span_pair_eq_of_eq_mul_unit _ _ _ uH hH₀⟩

theorem modularEval_mem_integralCoeffs {L : Type*} [CommRing L] (A : Subring L) (N : ℕ) [NeZero N]
    (p : MvPolynomial (Fin 2) A) : modularEval N A p ∈ CharPReduction.integralCoeffs A := by
  refine CharPReduction.modularRing_le_integralCoeffs N A ?_
  induction p using MvPolynomial.induction_on with
  | C c => rw [modularEval, eval₂Hom_C]; exact CharPReduction.constSeries_mem_modularRing N A c
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [modularEval, eval₂Hom_X']
    fin_cases i
    · exact CharPReduction.jqModC_mem_modularRing N A
    · exact CharPReduction.jqNModC_mem_modularRing N A

theorem pointEval_C {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k) (c : A) :
    pointEval A red a b (C c) = red c := by
  rw [pointEval, eval₂Hom_C]

theorem modularEval_C {L : Type*} [CommRing L] (A : Subring L) (N : ℕ) [NeZero N] (c : A) :
    modularEval N A (C c) = CharPReduction.constSeries A c := by
  rw [modularEval, eval₂Hom_C]

theorem pointEval_eq_apply_eval {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)
    (x y : A) (p : MvPolynomial (Fin 2) A) :
    pointEval A red (red x) (red y) p = red (MvPolynomial.eval ![x, y] p) := by
  have hfun : (![red x, red y] : Fin 2 → k) = red ∘ ![x, y] := by
    funext i; fin_cases i <;> simp
  rw [pointEval, coe_eval₂Hom, hfun, MvPolynomial.eval, coe_eval₂Hom, eval₂_comp_left, RingHom.comp_id]

theorem constSeries_comp_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : coeffSubring A K ≤ coeffSubring A K') :
    (CharPReduction.constSeries (coeffSubring A K')).comp (Subring.inclusion hle) =
      CharPReduction.constSeries (coeffSubring A K) :=
  RingHom.ext fun _ => rfl

theorem constSeries_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : coeffSubring A K ≤ coeffSubring A K')
    (c : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K') (Subring.inclusion hle c) =
      CharPReduction.constSeries (coeffSubring A K) c := rfl

theorem modularEval_map_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : coeffSubring A K ≤ coeffSubring A K')
    (N : ℕ) [NeZero N] (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval N (coeffSubring A K') (MvPolynomial.map (Subring.inclusion hle) p) =
      modularEval N (coeffSubring A K) p := by
  rw [modularEval, modularEval, eval₂Hom_map_hom, constSeries_comp_inclusion]

theorem redRestrict_comp_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : coeffSubring A K ≤ coeffSubring A K')
    {k : Type*} [Field k] (red : A →+* k) :
    (redRestrict red K').comp (Subring.inclusion hle) = redRestrict red K :=
  RingHom.ext fun _ => rfl

theorem redRestrict_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : coeffSubring A K ≤ coeffSubring A K')
    {k : Type*} [Field k] (red : A →+* k) (c : ↥(coeffSubring A K)) :
    redRestrict red K' (Subring.inclusion hle c) = redRestrict red K c := rfl

theorem pointEval_map_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : coeffSubring A K ≤ coeffSubring A K')
    {k : Type*} [Field k] (red : A →+* k) (b₀ b₁ : k) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    pointEval (coeffSubring A K') (redRestrict red K') b₀ b₁ (MvPolynomial.map (Subring.inclusion hle) p) =
      pointEval (coeffSubring A K) (redRestrict red K) b₀ b₁ p := by
  rw [pointEval, pointEval, eval₂Hom_map_hom, redRestrict_comp_inclusion]

theorem modularLocalizedAtPoint_mono {A : ValuationSubring (AlgebraicClosure ℚ)}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : coeffSubring A K ≤ coeffSubring A K')
    {k : Type*} [Field k] (red : A →+* k) (N : ℕ) [NeZero N] (b₀ b₁ : k) :
    modularLocalizedAtPoint N (coeffSubring A K) (redRestrict red K) b₀ b₁ ≤
      modularLocalizedAtPoint N (coeffSubring A K') (redRestrict red K') b₀ b₁ := by
  rintro f ⟨r, s, hs, hf⟩
  exact ⟨MvPolynomial.map (Subring.inclusion hle) r, MvPolynomial.map (Subring.inclusion hle) s,
    by rwa [pointEval_map_inclusion], by rwa [modularEval_map_inclusion, modularEval_map_inclusion]⟩

theorem isDiscreteValuationRing_coeffSubring {A : ValuationSubring (AlgebraicClosure ℚ)} (q : ℕ) [Fact q.Prime]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso
    have hqK : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
      rw [h]; exact (K.inv_mem (natCast_mem K q) : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ K)
    have h1 : redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) * redRestrict red K ⟨_, hqK⟩ = 1 := by
      rw [← map_mul, ← map_one (redRestrict red K)]
      congr 1
      apply Subtype.ext
      push_cast
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    rw [map_natCast, CharP.cast_eq_zero, zero_mul] at h1
    exact zero_ne_one h1
  · exact h

theorem isUnit_of_redRestrict_ne_zero {A : ValuationSubring (AlgebraicClosure ℚ)} (q : ℕ) [Fact q.Prime]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {c : ↥(coeffSubring A K)} (hc : redRestrict red K c ≠ 0) : IsUnit c := by
  have hdvr := isDiscreteValuationRing_coeffSubring q red K
  by_contra hu
  have hmem : c ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := hu
  have hker : (RingHom.ker (redRestrict red K)).IsMaximal := by
    have hprime : (RingHom.ker (redRestrict red K)).IsPrime := RingHom.ker_isPrime _
    have hne : RingHom.ker (redRestrict red K) ≠ ⊥ := by
      intro h0
      have hq : ((q : ℕ) : ↥(coeffSubring A K)) ∈ RingHom.ker (redRestrict red K) := by
        rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
      rw [h0, Ideal.mem_bot] at hq
      have hq' := congrArg Subtype.val hq
      push_cast at hq'
      exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hq'
    exact hprime.isMaximal hne
  rw [← IsLocalRing.eq_maximalIdeal hker, RingHom.mem_ker] at hmem
  exact hc hmem

theorem uniformizer_ne_zero {A : ValuationSubring (AlgebraicClosure ℚ)} (q : ℕ) [Fact q.Prime]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ϖ ≠ 0 := by
  intro h0
  obtain ⟨d, hd⟩ := (hϖ (q : ℕ)).mp (by rw [map_natCast, CharP.cast_eq_zero])
  rw [h0, zero_mul] at hd
  have hq' := congrArg Subtype.val hd
  push_cast at hq'
  exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hq'

theorem exists_split {A : ValuationSubring (AlgebraicClosure ℚ)} {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hle : coeffSubring A K ≤ coeffSubring A K') (ζ : ↥(coeffSubring A K'))
    (hbasis : ∀ c : ↥(coeffSubring A K'), ∃ c₀ c₁ : ↥(coeffSubring A K),
      c = Subring.inclusion hle c₀ + ζ * Subring.inclusion hle c₁)
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K')) :
    ∃ p₀ p₁ : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      p = MvPolynomial.map (Subring.inclusion hle) p₀ + C ζ * MvPolynomial.map (Subring.inclusion hle) p₁ := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨c₀, c₁, hc⟩ := hbasis c
    exact ⟨C c₀, C c₁, by rw [map_C, map_C, hc, C_add, C_mul]⟩
  | add p r hp hr =>
    obtain ⟨p₀, p₁, hp⟩ := hp
    obtain ⟨r₀, r₁, hr⟩ := hr
    exact ⟨p₀ + r₀, p₁ + r₁, by rw [hp, hr, map_add, map_add]; ring⟩
  | mul_X p i hp =>
    obtain ⟨p₀, p₁, hp⟩ := hp
    refine ⟨p₀ * X i, p₁ * X i, ?_⟩
    rw [hp]
    simp only [map_mul, map_X]
    ring

theorem mul_conj_eq_map {A : ValuationSubring (AlgebraicClosure ℚ)} {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hle : coeffSubring A K ≤ coeffSubring A K') (ζ : ↥(coeffSubring A K')) (α β : ↥(coeffSubring A K))
    (hζ : ζ ^ 2 = Subring.inclusion hle α * ζ + Subring.inclusion hle β)
    (p₀ p₁ : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    (MvPolynomial.map (Subring.inclusion hle) p₀ + C ζ * MvPolynomial.map (Subring.inclusion hle) p₁) *
      (MvPolynomial.map (Subring.inclusion hle) p₀ +
        (C (Subring.inclusion hle α) - C ζ) * MvPolynomial.map (Subring.inclusion hle) p₁) =
      MvPolynomial.map (Subring.inclusion hle) (p₀ ^ 2 + C α * p₀ * p₁ - C β * p₁ ^ 2) := by
  have hZ : (C ζ : MvPolynomial (Fin 2) ↥(coeffSubring A K')) ^ 2 =
      C (Subring.inclusion hle α) * C ζ + C (Subring.inclusion hle β) := by
    rw [← C_pow, hζ, C_add, C_mul]
  simp only [map_sub, map_add, map_pow, map_mul, map_C]
  linear_combination (-(MvPolynomial.map (Subring.inclusion hle) p₁) ^ 2) * hZ

theorem exists_redRestrict_eq_pointEval {A : ValuationSubring (AlgebraicClosure ℚ)} (q : ℕ)
    {k : Type*} [Field k] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (a : k) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    ∃ c : ↥(coeffSubring A K), redRestrict red K c = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p := by
  refine ⟨MvPolynomial.eval ![x, x ^ q] p, ?_⟩
  rw [← hx, ← map_pow, pointEval_eq_apply_eval]

theorem pointEval_conj_ne_zero {A : ValuationSubring (AlgebraicClosure ℚ)} {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hle : coeffSubring A K ≤ coeffSubring A K') (ζ : ↥(coeffSubring A K')) (α β : ↥(coeffSubring A K))
    (hζ : ζ ^ 2 = Subring.inclusion hle α * ζ + Subring.inclusion hle β)
    (q : ℕ) [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k) [FiniteDimensional ℚ K]
    (hirr : ∀ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 - α * c - β) ≠ 0)
    (a : k) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (s₀ s₁ : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs : pointEval (coeffSubring A K') (redRestrict red K') a (a ^ q)
      (MvPolynomial.map (Subring.inclusion hle) s₀ + C ζ * MvPolynomial.map (Subring.inclusion hle) s₁) ≠ 0) :
    pointEval (coeffSubring A K') (redRestrict red K') a (a ^ q)
      (MvPolynomial.map (Subring.inclusion hle) s₀ +
        (C (Subring.inclusion hle α) - C ζ) * MvPolynomial.map (Subring.inclusion hle) s₁) ≠ 0 := by
  set u := pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s₀ with hu
  set v := pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s₁ with hv
  set z := redRestrict red K' ζ with hz
  have hval1 : pointEval (coeffSubring A K') (redRestrict red K') a (a ^ q)
      (MvPolynomial.map (Subring.inclusion hle) s₀ + C ζ * MvPolynomial.map (Subring.inclusion hle) s₁) = u + z * v := by
    rw [map_add, map_mul, pointEval_map_inclusion, pointEval_map_inclusion, pointEval_C]
  have hval2 : pointEval (coeffSubring A K') (redRestrict red K') a (a ^ q)
      (MvPolynomial.map (Subring.inclusion hle) s₀ +
        (C (Subring.inclusion hle α) - C ζ) * MvPolynomial.map (Subring.inclusion hle) s₁) =
      u + (redRestrict red K α - z) * v := by
    rw [map_add, map_mul, map_sub, pointEval_map_inclusion, pointEval_map_inclusion, pointEval_C, pointEval_C]
    rfl
  have hz2 : z ^ 2 = redRestrict red K α * z + redRestrict red K β := by
    have h := congrArg (redRestrict red K') hζ
    rw [map_pow, map_add, map_mul] at h
    exact h
  rw [hval1] at hs
  rw [hval2]
  intro h0
  by_cases hv0 : v = 0
  · apply hs
    rw [hv0, mul_zero, add_zero] at h0 ⊢
    exact h0
  · obtain ⟨u', hu'⟩ := exists_redRestrict_eq_pointEval q red K a x hx s₀
    obtain ⟨v', hv'⟩ := exists_redRestrict_eq_pointEval q red K a x hx s₁
    rw [← hu] at hu'
    rw [← hv] at hv'
    have hv'0 : redRestrict red K v' ≠ 0 := by rw [hv']; exact hv0
    obtain ⟨vU, hvU⟩ := isUnit_of_redRestrict_ne_zero q red K hv'0
    set t : ↥(coeffSubring A K) := (u' + α * v') * ↑vU⁻¹ with ht
    have ht1 : redRestrict red K t * v = z * v := by
      have h1 : u + redRestrict red K α * v = z * v := by
        have : u + (redRestrict red K α - z) * v + z * v = z * v := by rw [h0, zero_add]
        rw [← this]; ring
      rw [← h1, ← hu', ← hv', ← map_mul, ← map_mul, ← map_add, ht]
      congr 1
      rw [← hvU, mul_assoc, Units.inv_mul, mul_one]
    have ht2 : redRestrict red K t = z := mul_right_cancel₀ hv0 ht1
    apply hirr t
    rw [map_sub, map_sub, map_mul, map_pow, ht2, hz2]
    ring

theorem inclusion_injective' {L : Type*} [Ring L] {S T : Subring L} (h : S ≤ T) :
    Function.Injective (Subring.inclusion h) :=
  fun a b hab => Subtype.ext (congrArg Subtype.val hab :)

theorem eq_zero_of_add_constSeries_mul_eq_zero {A : ValuationSubring (AlgebraicClosure ℚ)}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hle : coeffSubring A K ≤ coeffSubring A K') (ζ : ↥(coeffSubring A K')) (α β : ↥(coeffSubring A K))
    (hζ : ζ ^ 2 = Subring.inclusion hle α * ζ + Subring.inclusion hle β)
    {k : Type*} [Field k] (red : A →+* k)
    (hirr : ∀ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 - α * c - β) ≠ 0)
    {g₀ g₁ : LaurentSeries (AlgebraicClosure ℚ)}
    (hg₀ : g₀ ∈ CharPReduction.integralCoeffs (coeffSubring A K))
    (hg₁ : g₁ ∈ CharPReduction.integralCoeffs (coeffSubring A K))
    (h : g₀ + CharPReduction.constSeries (coeffSubring A K') ζ * g₁ = 0) : g₁ = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ : ∃ n, g₁.coeff n ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (by ext m; simp [hall m])
  have hC : CharPReduction.constSeries (coeffSubring A K') ζ =
      HahnSeries.single 0 ((ζ : AlgebraicClosure ℚ)) := by
    show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ζ : AlgebraicClosure ℚ) = _
    exact ModularCurve.algebraMap_laurentSeries_eq_single (AlgebraicClosure ℚ) (ζ : AlgebraicClosure ℚ)
  have hc := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff n) h
  simp only [hC, HahnSeries.coeff_add, HahnSeries.coeff_single_zero_mul, HahnSeries.coeff_zero] at hc

  have hζK : (ζ : AlgebraicClosure ℚ) ∈ K := by
    have e : (ζ : AlgebraicClosure ℚ) = -(g₀.coeff n) / g₁.coeff n := by
      field_simp
      linear_combination hc
    rw [e]
    have h0 : g₀.coeff n ∈ K := (Subring.mem_inf.mp (hg₀ n)).2
    have h1 : g₁.coeff n ∈ K := (Subring.mem_inf.mp (hg₁ n)).2
    exact div_mem (neg_mem h0) h1
  set c : ↥(coeffSubring A K) := ⟨ζ, Subring.mem_inf.mpr ⟨(Subring.mem_inf.mp ζ.2).1, hζK⟩⟩ with hcdef
  have hcζ : Subring.inclusion hle c = ζ := Subtype.ext rfl
  have hpoly : c ^ 2 - α * c - β = 0 := by
    apply inclusion_injective' hle
    rw [map_sub, map_sub, map_mul, map_pow, hcζ, map_zero, hζ]
    ring
  exact hirr c (by rw [hpoly, map_zero])

theorem coeff_decomp_eq_zero {A : ValuationSubring (AlgebraicClosure ℚ)} {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hle : coeffSubring A K ≤ coeffSubring A K') (ζ : ↥(coeffSubring A K')) (α β : ↥(coeffSubring A K))
    (hζ : ζ ^ 2 = Subring.inclusion hle α * ζ + Subring.inclusion hle β)
    {k : Type*} [Field k] (red : A →+* k)
    (hirr : ∀ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 - α * c - β) ≠ 0)
    {d₀ d₁ : ↥(coeffSubring A K)} (h : Subring.inclusion hle d₀ + ζ * Subring.inclusion hle d₁ = 0) :
    d₀ = 0 ∧ d₁ = 0 := by
  have h' : CharPReduction.constSeries (coeffSubring A K) d₀ +
      CharPReduction.constSeries (coeffSubring A K') ζ * CharPReduction.constSeries (coeffSubring A K) d₁ = 0 := by
    have := congrArg (CharPReduction.constSeries (coeffSubring A K')) h
    rw [map_add, map_mul, map_zero, constSeries_inclusion, constSeries_inclusion] at this
    exact this
  have h1 := eq_zero_of_add_constSeries_mul_eq_zero hle ζ α β hζ red hirr
    (CharPReduction.constSeries_mem_integralCoeffs _ d₀) (CharPReduction.constSeries_mem_integralCoeffs _ d₁) h'
  have hd₁ : d₁ = 0 := by
    have : ((d₁ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) = 0 :=
      (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective
        (by rw [map_zero]; exact h1)
    exact Subtype.ext this
  refine ⟨?_, hd₁⟩
  rw [hd₁, map_zero, mul_zero, add_zero] at h
  exact inclusion_injective' hle (by rw [h, map_zero])

theorem exists_decomp {A : ValuationSubring (AlgebraicClosure ℚ)} {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hle : coeffSubring A K ≤ coeffSubring A K') (ζ : ↥(coeffSubring A K')) (α β : ↥(coeffSubring A K))
    (hζ : ζ ^ 2 = Subring.inclusion hle α * ζ + Subring.inclusion hle β)
    (q : ℕ) [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k) [FiniteDimensional ℚ K]
    (hirr : ∀ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 - α * c - β) ≠ 0)
    (hbasis : ∀ c : ↥(coeffSubring A K'), ∃ c₀ c₁ : ↥(coeffSubring A K),
      c = Subring.inclusion hle c₀ + ζ * Subring.inclusion hle c₁)
    (a : k) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (f : LaurentSeries (AlgebraicClosure ℚ))
    (hf : f ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) :
    ∃ f₀ f₁ : LaurentSeries (AlgebraicClosure ℚ),
      f₀ ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ∧
      f₁ ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ∧
      f = f₀ + CharPReduction.constSeries (coeffSubring A K') ζ * f₁ := by
  obtain ⟨r, s, hs, hfs⟩ := hf
  obtain ⟨s₀, s₁, hs01⟩ := exists_split hle ζ hbasis s
  set ι := Subring.inclusion hle with hι
  set st := MvPolynomial.map ι s₀ + (C (ι α) - C ζ) * MvPolynomial.map ι s₁ with hst
  set N₀ := s₀ ^ 2 + C α * s₀ * s₁ - C β * s₁ ^ 2 with hN₀
  have hsst : s * st = MvPolynomial.map ι N₀ := by
    rw [hs01]; exact mul_conj_eq_map hle ζ α β hζ s₀ s₁
  have hst_ne : pointEval (coeffSubring A K') (redRestrict red K') a (a ^ q) st ≠ 0 :=
    pointEval_conj_ne_zero hle ζ α β hζ q red hirr a x hx s₀ s₁ (by rw [← hs01]; exact hs)
  have hN₀_ne : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) N₀ ≠ 0 := by
    rw [← pointEval_map_inclusion hle red, ← hsst, map_mul]
    exact mul_ne_zero hs hst_ne
  have hevN₀ : modularEval (1 * q) (coeffSubring A K) N₀ ≠ 0 := fun h0 =>
    hN₀_ne (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K N₀ h0)
  obtain ⟨t₀, t₁, ht01⟩ := exists_split hle ζ hbasis (r * st)
  have key : f * modularEval (1 * q) (coeffSubring A K) N₀ =
      modularEval (1 * q) (coeffSubring A K) t₀ +
        CharPReduction.constSeries (coeffSubring A K') ζ * modularEval (1 * q) (coeffSubring A K) t₁ := by
    have h1 : f * modularEval (1 * q) (coeffSubring A K') (MvPolynomial.map ι N₀) =
        modularEval (1 * q) (coeffSubring A K') (r * st) := by
      rw [← hsst, map_mul, ← mul_assoc, hfs, map_mul]
    rw [modularEval_map_inclusion] at h1
    rw [h1, ht01, map_add, map_mul, modularEval_map_inclusion, modularEval_map_inclusion, modularEval_C]
  refine ⟨modularEval (1 * q) (coeffSubring A K) t₀ * (modularEval (1 * q) (coeffSubring A K) N₀)⁻¹,
    modularEval (1 * q) (coeffSubring A K) t₁ * (modularEval (1 * q) (coeffSubring A K) N₀)⁻¹,
    ⟨t₀, N₀, hN₀_ne, by rw [mul_assoc, inv_mul_cancel₀ hevN₀, mul_one]⟩,
    ⟨t₁, N₀, hN₀_ne, by rw [mul_assoc, inv_mul_cancel₀ hevN₀, mul_one]⟩, ?_⟩
  calc f = f * modularEval (1 * q) (coeffSubring A K) N₀ * (modularEval (1 * q) (coeffSubring A K) N₀)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hevN₀, mul_one]
    _ = _ := by rw [key]; ring

theorem decomp_unique {A : ValuationSubring (AlgebraicClosure ℚ)} {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hle : coeffSubring A K ≤ coeffSubring A K') (ζ : ↥(coeffSubring A K')) (α β : ↥(coeffSubring A K))
    (hζ : ζ ^ 2 = Subring.inclusion hle α * ζ + Subring.inclusion hle β)
    (q : ℕ) [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hirr : ∀ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 - α * c - β) ≠ 0) (a : k)
    {f₀ f₁ g₀ g₁ : LaurentSeries (AlgebraicClosure ℚ)}
    (hf₀ : f₀ ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hf₁ : f₁ ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hg₀ : g₀ ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hg₁ : g₁ ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (h : f₀ + CharPReduction.constSeries (coeffSubring A K') ζ * f₁ =
      g₀ + CharPReduction.constSeries (coeffSubring A K') ζ * g₁) : f₀ = g₀ ∧ f₁ = g₁ := by
  set Z := CharPReduction.constSeries (coeffSubring A K') ζ with hZ
  have hd₀ : f₀ - g₀ ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := sub_mem hf₀ hg₀
  have hd₁ : f₁ - g₁ ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := sub_mem hf₁ hg₁
  obtain ⟨r₀, s₀, hs₀, hd0⟩ := hd₀
  obtain ⟨r₁, s₁, hs₁, hd1⟩ := hd₁
  have hev₀ : modularEval (1 * q) (coeffSubring A K) s₀ ≠ 0 := fun h0 =>
    hs₀ (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s₀ h0)
  have hev₁ : modularEval (1 * q) (coeffSubring A K) s₁ ≠ 0 := fun h0 =>
    hs₁ (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s₁ h0)
  have hsum : (f₀ - g₀) + Z * (f₁ - g₁) = 0 := by rw [hZ]; linear_combination h
  have hsum2 : modularEval (1 * q) (coeffSubring A K) (r₀ * s₁) +
      Z * modularEval (1 * q) (coeffSubring A K) (r₁ * s₀) = 0 := by
    rw [map_mul, map_mul, ← hd0, ← hd1]
    calc (f₀ - g₀) * modularEval (1 * q) (↑(coeffSubring A K)) s₀ * modularEval (1 * q) (↑(coeffSubring A K)) s₁ +
          Z * ((f₁ - g₁) * modularEval (1 * q) (↑(coeffSubring A K)) s₁ * modularEval (1 * q) (↑(coeffSubring A K)) s₀)
        = ((f₀ - g₀) + Z * (f₁ - g₁)) * modularEval (1 * q) (↑(coeffSubring A K)) s₀ *
            modularEval (1 * q) (↑(coeffSubring A K)) s₁ := by ring
      _ = 0 := by rw [hsum, zero_mul, zero_mul]
  have h1 := eq_zero_of_add_constSeries_mul_eq_zero hle ζ α β hζ red hirr
    (modularEval_mem_integralCoeffs _ _ _) (modularEval_mem_integralCoeffs _ _ _) hsum2
  rw [map_mul] at h1
  rcases mul_eq_zero.mp h1 with h1 | h1
  ·
    have hfg1 : f₁ - g₁ = 0 := by
      have := hd1; rw [h1] at this
      rcases mul_eq_zero.mp this with h2 | h2
      · exact h2
      · exact absurd h2 hev₁
    have hfg0 : f₀ - g₀ = 0 := by
      rw [hfg1, mul_zero, add_zero] at hsum; exact hsum
    exact ⟨sub_eq_zero.mp hfg0, sub_eq_zero.mp hfg1⟩
  · exact absurd h1 hev₀

end ModularCurve.NodeLocalized.InertDescent

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic.ModularCurve.NodeLocalized"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K']
    (hle : coeffSubring A K ≤ coeffSubring A K')
    (ζ : ↥(coeffSubring A K')) (α β : ↥(coeffSubring A K))
    (hζ : ζ ^ 2 = Subring.inclusion hle α * ζ + Subring.inclusion hle β)
    (hirr : ∀ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 - α * c - β) ≠ 0)
    (hbasis : ∀ c : ↥(coeffSubring A K'), ∃ c₀ c₁ : ↥(coeffSubring A K),
      c = Subring.inclusion hle c₀ + ζ * Subring.inclusion hle c₁)
    (hϖ' : ∀ c : ↥(coeffSubring A K'), redRestrict red K' c = 0 ↔ ∃ d, c = Subring.inclusion hle ϖ * d)
    (hK' :
    ∃ (eK : ℕ) (ε : ↥(coeffSubring A K')), 1 ≤ eK ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K')) = Subring.inclusion hle ϖ ^ eK * ε ∧
    ∃ (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))),
      IsUnit w ∧
      G' * H' = (⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))) ^ (jWidth a * eK) * w ∧
      (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))],
        IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) =
          Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))), G', H'}) ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))), G'}).IsPrime ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))), H'}).IsPrime ∧
      H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))), G'} ∧
      G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))), H'} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)))} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)))}) :
    ∃ (eK : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      IsUnit w ∧
      G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (jWidth a * eK) * w ∧
      (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
        IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
          Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'}) ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}).IsPrime ∧
      H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} ∧
      G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} := by
  classical

  obtain ⟨_, hLoc, -, -⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  obtain ⟨_, hLoc', -, -⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K'
      (Subring.inclusion hle x) ((InertDescent.redRestrict_inclusion hle red x).trans hx) (Subring.inclusion hle ϖ) hϖ'
  haveI := hLoc
  haveI := hLoc'
  obtain ⟨eK, ε', heK, hε', hqε', G'', H'', w'', hw'', hGH'', hmax', hP', hQ', hHn', hGn', hpinG', hpinH'⟩ := hK'
  have hmax'' := @hmax' hLoc'
  clear hmax'

  have hRR' : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ≤
      modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) :=
    InertDescent.modularLocalizedAtPoint_mono hle red (1 * q) a (a ^ q)
  set φ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) := Subring.inclusion hRR' with hφdef

  set πR := (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) with hπRdef
  set gR := (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) with hgRdef
  set hR := (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) with hhRdef

  have eπ : (⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))) = φ πR := by
    apply Subtype.ext
    show modularEval (1 * q) (coeffSubring A K') (MvPolynomial.C (Subring.inclusion hle ϖ)) =
      modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ)
    rw [← MvPolynomial.map_C (Subring.inclusion hle), InertDescent.modularEval_map_inclusion]
  have eg : (⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))) = φ gR := by
    apply Subtype.ext
    show modularEval (1 * q) (coeffSubring A K') (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) =
      modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)
    rw [← InertDescent.modularEval_map_inclusion hle (1 * q)]
    simp only [map_sub, map_pow, MvPolynomial.map_X]
  have eh : (⟨modularEval (1 * q) (coeffSubring A K') (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))) = φ hR := by
    apply Subtype.ext
    show modularEval (1 * q) (coeffSubring A K') (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) =
      modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
    rw [← InertDescent.modularEval_map_inclusion hle (1 * q)]
    simp only [map_sub, map_pow, MvPolynomial.map_X]
  rw [eπ] at hGH'' hmax'' hP' hQ' hHn' hGn' hpinG' hpinH'
  rw [eg] at hpinG'
  rw [eh] at hpinH'

  have hϖ0 : ϖ ≠ 0 := InertDescent.uniformizer_ne_zero q red K ϖ hϖ
  have hπ0 : πR ≠ 0 := by
    intro h0
    have h1 : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ) = 0 := congrArg Subtype.val h0
    rw [InertDescent.modularEval_C] at h1
    have h2 : ((ϖ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) = 0 :=
      (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective (by rw [map_zero]; exact h1)
    exact hϖ0 (Subtype.ext h2)

  have hζmem : CharPReduction.constSeries (coeffSubring A K') ζ ∈
      modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) := by
    rw [← InertDescent.modularEval_C _ (1 * q)]
    exact modularEval_mem_modularLocalizedAtPoint _ _ _ _ _ _
  set ζR : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) := ⟨_, hζmem⟩ with hζRdef
  have decomp : ∀ f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)), ∃ f₀ f₁ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)), f = φ f₀ + ζR * φ f₁ := by
    intro f
    obtain ⟨f₀, f₁, hf₀, hf₁, hf⟩ := InertDescent.exists_decomp hle ζ α β hζ q red hirr hbasis a x hx f.1 f.2
    exact ⟨⟨f₀, hf₀⟩, ⟨f₁, hf₁⟩, Subtype.ext hf⟩
  have uniq : ∀ f₀ f₁ g₀ g₁ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)), φ f₀ + ζR * φ f₁ = φ g₀ + ζR * φ g₁ → f₀ = g₀ ∧ f₁ = g₁ := by
    intro f₀ f₁ g₀ g₁ hfg
    have h' : (f₀ : LaurentSeries (AlgebraicClosure ℚ)) + CharPReduction.constSeries (coeffSubring A K') ζ * f₁ =
        g₀ + CharPReduction.constSeries (coeffSubring A K') ζ * g₁ := congrArg Subtype.val hfg
    have := InertDescent.decomp_unique hle ζ α β hζ q red hirr a f₀.2 f₁.2 g₀.2 g₁.2 h'
    exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩

  obtain ⟨G₀, H₀, w₀, hw₀, hGH₀, hmax₀, hspanG, hspanH⟩ :=
    InertDescent.core φ ζR decomp uniq πR gR hR hπ0 (jWidth a * eK) G'' H'' w'' hw'' hGH'' hmax'' hP' hQ' hHn' hGn'
      hpinG' hpinH'

  obtain ⟨c₀, c₁, hc01⟩ := hbasis ε'
  have hqε : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * c₀ ∧ ϖ ^ eK * c₁ = 0 := by
    have h1 : Subring.inclusion hle (ϖ ^ eK * c₀ - q) + ζ * Subring.inclusion hle (ϖ ^ eK * c₁) = 0 := by
      rw [map_sub, map_mul, map_pow, map_natCast, map_mul, map_pow, hqε', hc01]; ring
    obtain ⟨h2, h3⟩ := InertDescent.coeff_decomp_eq_zero hle ζ α β hζ red hirr h1
    exact ⟨(sub_eq_zero.mp h2).symm, h3⟩
  have hc₁ : c₁ = 0 := (mul_eq_zero.mp hqε.2).resolve_left (pow_ne_zero _ hϖ0)
  have hε'c : ε' = Subring.inclusion hle c₀ := by rw [hc01, hc₁, map_zero, mul_zero, add_zero]
  have hεu : IsUnit c₀ := by
    obtain ⟨v, hv⟩ := hε'.exists_right_inv
    obtain ⟨v₀, v₁, hv01⟩ := hbasis v
    have h1 : Subring.inclusion hle (c₀ * v₀ - 1) + ζ * Subring.inclusion hle (c₀ * v₁) = 0 := by
      rw [hε'c, hv01] at hv
      rw [map_sub, map_one, map_mul, map_mul]
      linear_combination hv
    exact isUnit_iff_exists_inv.mpr ⟨v₀, sub_eq_zero.mp (InertDescent.coeff_decomp_eq_zero hle ζ α β hζ red hirr h1).1⟩

  have hGHmem : G₀ * H₀ ∈ Ideal.span {πR} := by
    rw [hGH₀]
    obtain ⟨m, hm⟩ : ∃ m, jWidth a * eK = m + 1 :=
      ⟨jWidth a * eK - 1, by have := jWidth_pos a; have : 1 ≤ jWidth a * eK := Nat.mul_pos this heK; omega⟩
    rw [hm, pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  obtain ⟨hP₀, hQ₀, hHn₀, hGn₀, -, hor⟩ :=
    ModularCurve.NodeLocalized.span_uniformizer_pair_eq_branches_or_swap_of_maximalIdeal_eq_span red a ha2 K ϖ hϖ
      G₀ H₀ hGHmem hmax₀
  have hpins : Ideal.span {πR, G₀} = Ideal.span {πR, gR} ∧ Ideal.span {πR, H₀} = Ideal.span {πR, hR} := by
    rcases hor with hor | ⟨hswapG, -⟩
    · exact hor
    · exfalso
      apply hHn'
      have h1 : Ideal.span {φ πR, φ G₀} = Ideal.span {φ πR, φ hR} := by
        have := congrArg (Ideal.map φ) hswapG
        rwa [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_pair] at this
      rw [← hspanG, h1, ← hpinH']
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact ⟨eK, c₀, heK, hεu, hqε.1, G₀, H₀, w₀, hw₀, hGH₀, by intro _; exact hmax₀, hP₀, hQ₀, hHn₀, hGn₀, hpins.1, hpins.2⟩

end S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic
end P2MW
export P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_inertQuadratic (solution)
