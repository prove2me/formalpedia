-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_heightOnePrime_sectionOfCrossingParam_centred_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/bb82b9d7-f1cf-5e35-92c9-20d576208f21

import Mathlib
import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_heightOnePrime_sectionOfCrossingParam_centred_zero
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"

set_option autoImplicit false

noncomputable section

namespace CrossingSectionPrime

variable {R : Type*} [CommRing R] {π u v w c₀ : R} {n a : ℕ}

private theorem exists_eq_mul_of_mem_of_mem (hn : 1 ≤ n) (huv : u * v = π ^ n * w)
    (hQ' : (Ideal.span {π, v}).IsPrime) (huQ' : u ∉ Ideal.span {π, v})
    {t : R} (htQ : t ∈ Ideal.span {π, u}) (htQ' : t ∈ Ideal.span {π, v}) : ∃ z, t = π * z := by
  obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp htQ
  have hπQ' : π ∈ Ideal.span {π, v} := Ideal.subset_span (Set.mem_insert _ _)
  have hβu : β * u ∈ Ideal.span {π, v} := by
    have h : α * π + β * u - α * π ∈ Ideal.span {π, v} := sub_mem htQ' (Ideal.mul_mem_left _ _ hπQ')
    rwa [add_sub_cancel_left] at h
  have hβ : β ∈ Ideal.span {π, v} := (hQ'.mem_or_mem hβu).resolve_right huQ'
  obtain ⟨γ, δ, rfl⟩ := Ideal.mem_span_pair.mp hβ
  refine ⟨α + γ * u + δ * π ^ (n - 1) * w, ?_⟩
  have hn' : π ^ n = π * π ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  calc α * π + (γ * π + δ * v) * u = α * π + γ * π * u + δ * (u * v) := by ring
    _ = α * π + γ * π * u + δ * (π ^ n * w) := by rw [huv]
    _ = π * (α + γ * u + δ * π ^ (n - 1) * w) := by rw [hn']; ring

private theorem pi_ne_zero [IsDomain R] (han : a < n) (huv : u * v = π ^ n * w)
    (huQ' : u ∉ Ideal.span {π, v}) (hvQ : v ∉ Ideal.span {π, u}) : π ≠ 0 := by
  intro hπ
  have h0 : u * v = 0 := by
    rw [huv, hπ, zero_pow (by omega), zero_mul]
  rcases mul_eq_zero.mp h0 with hu | hv
  · exact huQ' (by rw [hu]; exact zero_mem _)
  · exact hvQ (by rw [hv]; exact zero_mem _)

private theorem sub_mul_v (han : a < n) (huv : u * v = π ^ n * w) :
    (u - π ^ a * c₀) * v = π ^ a * (π ^ (n - a) * w - c₀ * v) := by
  have hn : π ^ n = π ^ a * π ^ (n - a) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt han)]
  calc (u - π ^ a * c₀) * v = u * v - π ^ a * c₀ * v := by ring
    _ = π ^ a * π ^ (n - a) * w - π ^ a * c₀ * v := by rw [huv, hn]
    _ = π ^ a * (π ^ (n - a) * w - c₀ * v) := by ring

private theorem u_mul_y (han : a < n) (huv : u * v = π ^ n * w) :
    u * (π ^ (n - a) * w - c₀ * v) = π ^ (n - a) * w * (u - π ^ a * c₀) := by
  have hn : π ^ n = π ^ (n - a) * π ^ a := by
    rw [← pow_add, Nat.sub_add_cancel (le_of_lt han)]
  calc u * (π ^ (n - a) * w - c₀ * v) = π ^ (n - a) * w * u - c₀ * (u * v) := by ring
    _ = π ^ (n - a) * w * u - c₀ * (π ^ n * w) := by rw [huv]
    _ = π ^ (n - a) * w * (u - π ^ a * c₀) := by rw [hn]; ring

private theorem y_notMem (hc₀ : IsUnit c₀) (han : a < n) (hQ : (Ideal.span {π, u}).IsPrime)
    (hvQ : v ∉ Ideal.span {π, u}) : π ^ (n - a) * w - c₀ * v ∉ Ideal.span {π, u} := by
  intro hy
  have hπQ : π ∈ Ideal.span {π, u} := Ideal.subset_span (Set.mem_insert _ _)
  have hπw : π ^ (n - a) * w ∈ Ideal.span {π, u} :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπQ _ (by omega))
  have hcv : c₀ * v ∈ Ideal.span {π, u} := by
    have h := sub_mem hπw hy
    rwa [sub_sub_cancel] at h
  rcases hQ.mem_or_mem hcv with hc | hv
  · exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hc hc₀)
  · exact hvQ hv

private theorem sub_value_ne_zero (ha : 1 ≤ a) (huQ' : u ∉ Ideal.span {π, v}) : u - π ^ a * c₀ ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  apply huQ'
  rw [h]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_insert _ _)) _ (by omega))

private theorem sub_mul_ne_pow [IsDomain R] [IsLocalRing R] (hc₀ : IsUnit c₀) (ha : 1 ≤ a) (han : a < n)
    (huv : u * v = π ^ n * w) (hQ : (Ideal.span {π, u}).IsPrime) (hQ' : (Ideal.span {π, v}).IsPrime)
    (huQ' : u ∉ Ideal.span {π, v}) (hvQ : v ∉ Ideal.span {π, u}) :
    ∀ (N : ℕ) (t : R), (u - π ^ a * c₀) * t ≠ π ^ N := by
  have hπ0 : π ≠ 0 := pi_ne_zero han huv huQ' hvQ
  have hπQ : π ∈ Ideal.span {π, u} := Ideal.subset_span (Set.mem_insert _ _)
  have hπQ' : π ∈ Ideal.span {π, v} := Ideal.subset_span (Set.mem_insert _ _)
  have hcQ' : π ^ a * c₀ ∈ Ideal.span {π, v} :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπQ' _ (by omega))
  have hucQ' : u - π ^ a * c₀ ∉ Ideal.span {π, v} := by
    intro h
    exact huQ' (by simpa using add_mem h hcQ')
  have hy : π ^ (n - a) * w - c₀ * v ∉ Ideal.span {π, u} := y_notMem hc₀ han hQ hvQ
  have key : (u - π ^ a * c₀) * v = π ^ a * (π ^ (n - a) * w - c₀ * v) := sub_mul_v han huv

  have step : ∀ (N : ℕ) (t : R), (u - π ^ a * c₀) * t = π ^ N →
      π ^ a * ((π ^ (n - a) * w - c₀ * v) * t) = π ^ N * v := by
    intro N t ht
    calc π ^ a * ((π ^ (n - a) * w - c₀ * v) * t) = ((u - π ^ a * c₀) * v) * t := by rw [key]; ring
      _ = (u - π ^ a * c₀) * t * v := by ring
      _ = π ^ N * v := by rw [ht]

  have case_lt : ∀ (N : ℕ) (t : R), N < a → (u - π ^ a * c₀) * t ≠ π ^ N := by
    intro N t hN ht
    have h := step N t ht
    have ha' : π ^ a = π ^ N * π ^ (a - N) := by rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hN)]
    rw [ha', mul_assoc] at h
    have h' : π ^ (a - N) * ((π ^ (n - a) * w - c₀ * v) * t) = v := mul_left_cancel₀ (pow_ne_zero N hπ0) h
    have hmem : π ^ (a - N) * ((π ^ (n - a) * w - c₀ * v) * t) ∈ Ideal.span {π, u} :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπQ _ (by omega))
    rw [h'] at hmem
    exact hvQ hmem
  intro N
  induction N with
  | zero => intro t; exact case_lt 0 t (by omega)
  | succ N ih =>
      intro t ht
      rcases lt_trichotomy (N + 1) a with hlt | heq | hgt
      · exact case_lt (N + 1) t hlt ht
      ·
        have h := step (N + 1) t ht
        rw [heq] at h ht
        have h' : (π ^ (n - a) * w - c₀ * v) * t = v := mul_left_cancel₀ (pow_ne_zero a hπ0) h
        have h'' : v * (1 + c₀ * t) = π ^ (n - a) * w * t := by linear_combination (-1 : R) * h'
        have hmem : v * (1 + c₀ * t) ∈ Ideal.span {π, u} := by
          rw [h'']
          exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπQ _ (by omega)))
        have h1 : 1 + c₀ * t ∈ Ideal.span {π, u} := (hQ.mem_or_mem hmem).resolve_left hvQ
        have h1m : 1 + c₀ * t ∈ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hQ.ne_top h1
        have hct : IsUnit (c₀ * t) := by
          by_contra hnu
          have hm : c₀ * t ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
          have h1' : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
            have := sub_mem h1m hm
            rwa [add_sub_cancel_right] at this
          exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1' isUnit_one)
        obtain ⟨tu, rfl⟩ := (IsUnit.mul_iff.mp hct).2
        have hsub : u - π ^ a * c₀ = π ^ a * ↑tu⁻¹ := by
          calc u - π ^ a * c₀ = (u - π ^ a * c₀) * (↑tu * ↑tu⁻¹) := by rw [Units.mul_inv, mul_one]
            _ = π ^ a * ↑tu⁻¹ := by rw [← mul_assoc, ht]
        have hu : u = (u - π ^ a * c₀) + π ^ a * c₀ := by ring
        apply huQ'
        rw [hu, hsub]
        exact add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπQ' _ (by omega))) hcQ'
      ·
        have h := step (N + 1) t ht
        have hN1 : π ^ (N + 1) = π ^ a * π ^ (N + 1 - a) := by
          rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hgt)]
        rw [hN1, mul_assoc] at h
        have h' : (π ^ (n - a) * w - c₀ * v) * t = π ^ (N + 1 - a) * v :=
          mul_left_cancel₀ (pow_ne_zero a hπ0) h
        have htQ : t ∈ Ideal.span {π, u} := by
          have hmem : (π ^ (n - a) * w - c₀ * v) * t ∈ Ideal.span {π, u} := by
            rw [h']
            exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπQ _ (by omega))
          exact (hQ.mem_or_mem hmem).resolve_left hy
        have htQ' : t ∈ Ideal.span {π, v} := by
          have hmem : (u - π ^ a * c₀) * t ∈ Ideal.span {π, v} := by
            rw [ht]
            exact Ideal.pow_mem_of_mem _ hπQ' _ (by omega)
          exact (hQ'.mem_or_mem hmem).resolve_left hucQ'
        obtain ⟨t', rfl⟩ := exists_eq_mul_of_mem_of_mem (by omega) huv hQ' huQ' htQ htQ'
        apply ih t'
        have h2 : π * ((u - π ^ a * c₀) * t') = π * π ^ N := by
          rw [← pow_succ', ← ht]
          ring
        exact mul_left_cancel₀ hπ0 h2

private theorem le_of_isPrime (hc₀ : IsUnit c₀) (han : a < n) (huv : u * v = π ^ n * w)
    (P : Ideal R) (hP : P.IsPrime) (huc : u - π ^ a * c₀ ∈ P) (hπ : π ∉ P) :
    u ∉ P ∧ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} ≤ P := by
  have hu : u ∉ P := by
    intro hu
    have hc : π ^ a * c₀ ∈ P := by
      have := sub_mem hu huc
      rwa [sub_sub_cancel] at this
    rcases hP.mem_or_mem hc with h | h
    · exact hπ (hP.mem_of_pow_mem _ h)
    · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h hc₀)
  refine ⟨hu, ?_⟩
  rw [Ideal.span_le]
  rintro z (rfl | rfl)
  · exact huc
  · have hmem : u * (π ^ (n - a) * w - c₀ * v) ∈ P := by
      rw [u_mul_y han huv]
      exact Ideal.mul_mem_left _ _ huc
    exact (hP.mem_or_mem hmem).resolve_left hu

private theorem maximalIdeal_le_sup [IsLocalRing R] (hc₀ : IsUnit c₀) (ha : 1 ≤ a) (han : a < n)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {π, u, v}) :
    IsLocalRing.maximalIdeal R ≤ Ideal.span {π} ⊔ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} := by
  obtain ⟨c₀', hc₀'⟩ := hc₀.exists_right_inv
  have hπ : π ∈ Ideal.span {π} ⊔ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} :=
    Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
  have hJ1 : u - π ^ a * c₀ ∈ Ideal.span {π} ⊔ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} :=
    Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert _ _))
  have hJ2 : π ^ (n - a) * w - c₀ * v ∈ Ideal.span {π} ⊔ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} :=
    Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hu' : u ∈ Ideal.span {π} ⊔ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} := by
    have hx : u = (u - π ^ a * c₀) + π ^ (a - 1) * c₀ * π := by
      have : π ^ a = π ^ (a - 1) * π := by rw [← pow_succ, Nat.sub_add_cancel ha]
      rw [this]; ring
    have key : (u - π ^ a * c₀) + π ^ (a - 1) * c₀ * π
        ∈ Ideal.span {π} ⊔ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} :=
      add_mem hJ1 (Ideal.mul_mem_left _ _ hπ)
    rwa [← hx] at key
  have hv' : v ∈ Ideal.span {π} ⊔ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} := by
    have hx : v = c₀' * (π ^ (n - a - 1) * w) * π - c₀' * (π ^ (n - a) * w - c₀ * v) := by
      have hna : π ^ (n - a) = π ^ (n - a - 1) * π := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hna]
      linear_combination (-v) * hc₀'
    have key : c₀' * (π ^ (n - a - 1) * w) * π - c₀' * (π ^ (n - a) * w - c₀ * v)
        ∈ Ideal.span {π} ⊔ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} :=
      sub_mem (Ideal.mul_mem_left _ _ hπ) (Ideal.mul_mem_left _ _ hJ2)
    rwa [← hx] at key
  rw [hm, Ideal.span_le, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hπ, hu', hv'⟩

private theorem eq_of_isPrime [IsNoetherianRing R] [IsLocalRing R] (hc₀ : IsUnit c₀) (ha : 1 ≤ a) (han : a < n)
    (huv : u * v = π ^ n * w) (hm : IsLocalRing.maximalIdeal R = Ideal.span {π, u, v})
    (P : Ideal R) (hP : P.IsPrime) (huc : u - π ^ a * c₀ ∈ P) (hπ : π ∉ P) :
    P = Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} := by
  obtain ⟨-, hle⟩ := le_of_isPrime hc₀ han huv P hP huc hπ
  refine le_antisymm ?_ hle
  have hPm : P ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hP.ne_top
  have hπm : Ideal.span {π} ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff, hm]
    exact Ideal.subset_span (Set.mem_insert _ _)
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {π}) (IsNoetherian.noetherian P) ?_ ?_
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hπm
  · intro t ht
    have htm := maximalIdeal_le_sup (w := w) hc₀ ha han hm (hPm ht)
    obtain ⟨p, hp, j, hj, hpj⟩ := Submodule.mem_sup.mp htm
    obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    have hα : α * π ∈ P := by
      have : α * π = t - j := by rw [← hpj]; ring
      rw [this]
      exact sub_mem ht (hle hj)
    have hαP : α ∈ P := (hP.mem_or_mem hα).resolve_right hπ
    rw [← hpj]
    refine Submodule.mem_sup.mpr ⟨j, hj, α * π, ?_, by ring⟩
    rw [mul_comm]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) hαP

private theorem isPrime_and [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hc₀ : IsUnit c₀) (ha : 1 ≤ a) (han : a < n)
    (huv : u * v = π ^ n * w) (hm : IsLocalRing.maximalIdeal R = Ideal.span {π, u, v})
    (hQ : (Ideal.span {π, u}).IsPrime) (hQ' : (Ideal.span {π, v}).IsPrime)
    (huQ' : u ∉ Ideal.span {π, v}) (hvQ : v ∉ Ideal.span {π, u}) :
    (Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v}).IsPrime ∧
    π ∉ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} ∧
    u ∉ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} := by
  have hdisj : Disjoint ((Ideal.span {u - π ^ a * c₀} : Ideal R) : Set R) (Submonoid.powers π : Set R) := by
    rw [Set.disjoint_left]
    intro z hzI hzS
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hzI
    obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff _ _).mp hzS
    exact sub_mul_ne_pow hc₀ ha han huv hQ hQ' huQ' hvQ N t (by rw [mul_comm]; exact hN.symm)
  obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint (Ideal.span {u - π ^ a * c₀}) (Submonoid.powers π) hdisj
  have huc : u - π ^ a * c₀ ∈ P := hIP (Ideal.mem_span_singleton_self _)
  have hπ : π ∉ P := fun h => Set.disjoint_left.mp hPS h (Submonoid.mem_powers π)
  have hPJ := eq_of_isPrime hc₀ ha han huv hm P hP huc hπ
  obtain ⟨hu, -⟩ := le_of_isPrime hc₀ han huv P hP huc hπ
  rw [hPJ] at hP hπ hu
  exact ⟨hP, hπ, hu⟩

private theorem height_eq_one [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hc₀ : IsUnit c₀) (ha : 1 ≤ a) (han : a < n)
    (huv : u * v = π ^ n * w) (hm : IsLocalRing.maximalIdeal R = Ideal.span {π, u, v})
    (hQ : (Ideal.span {π, u}).IsPrime) (hQ' : (Ideal.span {π, v}).IsPrime)
    (huQ' : u ∉ Ideal.span {π, v}) (hvQ : v ∉ Ideal.span {π, u}) (hdim : ringKrullDim R = 2) :
    (Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v}).height = 1 := by
  obtain ⟨hJ, hπJ, -⟩ := isPrime_and hc₀ ha han huv hm hQ hQ' huQ' hvQ
  haveI := hJ

  have hJ0 : (⊥ : Ideal R) < Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} := by
    rw [bot_lt_iff_ne_bot]
    intro h0
    have hmem : u - π ^ a * c₀ ∈ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h0, Ideal.mem_bot] at hmem
    exact sub_value_ne_zero ha huQ' hmem

  have hJm : Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v} < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hJ.ne_top) ?_
    intro h
    apply hπJ
    rw [h, hm]
    exact Ideal.subset_span (Set.mem_insert _ _)

  have hmh : (IsLocalRing.maximalIdeal R).height = ((2 : ℕ) : ℕ∞) := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hdim] at h
    have h' : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [h]
      rfl
    exact WithBot.coe_eq_coe.mp h'
  have hJlt : (Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v}).height < ((2 : ℕ) : ℕ∞) :=
    (Ideal.height_le_iff.mp hmh.le) _ hJ hJm
  have hJle : (Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v}).height ≤ 1 := by
    have h2 : ((2 : ℕ) : ℕ∞) = (1 : ℕ∞) + 1 := by norm_num
    rw [h2] at hJlt
    exact (ENat.lt_add_one_iff ENat.one_ne_top).mp hJlt
  have hJge : 1 ≤ (Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v}).height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hJ0
    rwa [Ideal.height_bot, zero_add] at h
  exact le_antisymm hJle hJge

private theorem exists_mul_eq_of_mem (han : a < n) (huv : u * v = π ^ n * w) {t : R}
    (ht : t ∈ Ideal.span {u - π ^ a * c₀, π ^ (n - a) * w - c₀ * v}) :
    ∃ α : R, t * u = (u - π ^ a * c₀) * α := by
  obtain ⟨β, γ, rfl⟩ := Ideal.mem_span_pair.mp ht
  refine ⟨β * u + γ * (π ^ (n - a) * w), ?_⟩
  have h := u_mul_y (c₀ := c₀) han huv
  calc (β * (u - π ^ a * c₀) + γ * (π ^ (n - a) * w - c₀ * v)) * u
        = β * (u - π ^ a * c₀) * u + γ * (u * (π ^ (n - a) * w - c₀ * v)) := by ring
    _ = β * (u - π ^ a * c₀) * u + γ * (π ^ (n - a) * w * (u - π ^ a * c₀)) := by rw [h]
    _ = (u - π ^ a * c₀) * (β * u + γ * (π ^ (n - a) * w)) := by ring

private theorem exists_section_prime [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hc₀ : IsUnit c₀) (ha : 1 ≤ a)
    (han : a < n) (huv : u * v = π ^ n * w) (hm : IsLocalRing.maximalIdeal R = Ideal.span {π, u, v})
    (hQ : (Ideal.span {π, u}).IsPrime) (hQ' : (Ideal.span {π, v}).IsPrime)
    (huQ' : u ∉ Ideal.span {π, v}) (hvQ : v ∉ Ideal.span {π, u}) (hdim : ringKrullDim R = 2) :
    ∃ J : Ideal R, J.IsPrime ∧ π ∉ J ∧ u ∉ J ∧ J.height = 1 ∧ u - π ^ a * c₀ ∈ J ∧
      ∀ t ∈ J, ∃ α : R, t * u = (u - π ^ a * c₀) * α := by
  obtain ⟨hJ, hπJ, huJ⟩ := isPrime_and hc₀ ha han huv hm hQ hQ' huQ' hvQ
  exact ⟨_, hJ, hπJ, huJ, height_eq_one hc₀ ha han huv hm hQ hQ' huQ' hvQ hdim,
    Ideal.subset_span (Set.mem_insert _ _), fun _ ht => exists_mul_eq_of_mem han huv ht⟩

end CrossingSectionPrime

namespace NodeSectionPrime

open ModularCurve ModularCurve.NodeLocalized

variable (q : ℕ) {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

private theorem natCast_mem_maximalIdeal_valuationSubring [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
  (hker _).mp (by rw [map_natCast, CharP.cast_eq_zero])

private theorem redRestrict_eval (red : A →+* k) (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    redRestrict red K (MvPolynomial.eval ![x, x ^ q] p) = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p := by
  show ((redRestrict red K).comp (MvPolynomial.eval ![x, x ^ q])) p = (MvPolynomial.eval₂Hom (redRestrict red K) ![a, a ^ q]) p
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)) p
  · rw [RingHom.comp_apply, MvPolynomial.eval_C, MvPolynomial.eval₂Hom_C]
  · rw [RingHom.comp_apply, MvPolynomial.eval_X, MvPolynomial.eval₂Hom_X']
    simp [hx]
  · rw [RingHom.comp_apply, MvPolynomial.eval_X, MvPolynomial.eval₂Hom_X']
    simp [hx]

end NodeSectionPrime

namespace NodeSectionPrime

open ModularCurve ModularCurve.NodeLocalized

variable (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k]

section Coefficients

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem coeffSubring_le_valuationSubring : coeffSubring A K ≤ A.toSubring := inf_le_left

private def toA : ↥(coeffSubring A K) →+* ↥A := Subring.inclusion (coeffSubring_le_valuationSubring (A := A) K)

private theorem coe_toA (t : ↥(coeffSubring A K)) : ((toA K t : ↥A) : AlgebraicClosure ℚ) = t := rfl

private theorem redRestrict_apply (red : A →+* k) (t : ↥(coeffSubring A K)) : redRestrict red K t = red (toA K t) := rfl

private theorem coe_mem_field (t : ↥(coeffSubring A K)) : (t : AlgebraicClosure ℚ) ∈ K := t.2.2

private theorem isUnit_iff_isUnit_toA (t : ↥(coeffSubring A K)) : IsUnit t ↔ IsUnit (toA K t) := by
  refine ⟨fun h => h.map (toA K), fun h => ?_⟩
  obtain ⟨s, hs⟩ := h.exists_right_inv
  have hts : (t : AlgebraicClosure ℚ) * (s : AlgebraicClosure ℚ) = 1 := by
    have h1 := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hs
    simpa [coe_toA] using h1
  have hsK : (s : AlgebraicClosure ℚ) ∈ K := by
    rw [eq_inv_of_mul_eq_one_right hts]
    exact K.inv_mem (coe_mem_field K t)
  exact IsUnit.of_mul_eq_one (⟨(s : AlgebraicClosure ℚ), Subring.mem_inf.mpr ⟨s.2, hsK⟩⟩ : ↥(coeffSubring A K)) (Subtype.ext hts)

variable (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

include hker in

private theorem isDiscreteValuationRing_coeffSubring [CharP k q] [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso
    have hqm : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := natCast_mem_maximalIdeal_valuationSubring q red hker
    have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    have hinv : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
      rw [h]
      exact K.inv_mem (natCast_mem K q)
    have hinvA : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ A := (Subring.mem_inf.mp hinv).1
    have hunit : IsUnit ((q : ℕ) : ↥A) := by
      refine IsUnit.of_mul_eq_one ⟨_, hinvA⟩ (Subtype.ext ?_)
      push_cast
      exact mul_inv_cancel₀ hq0
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hqm) hunit
  · exact h

include hker in

private theorem redRestrict_eq_zero_iff (hdvr : IsDiscreteValuationRing ↥(coeffSubring A K))
    {ϖ' : ↥(coeffSubring A K)} (hirr : Irreducible ϖ') (t : ↥(coeffSubring A K)) :
    redRestrict red K t = 0 ↔ ∃ e, t = ϖ' * e := by
  haveI := hdvr
  rw [redRestrict_apply, hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_iff_isUnit_toA K t,
    ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hirr.maximalIdeal_eq, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [← he, mul_comm]⟩
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [he, mul_comm]⟩

include hker in

private theorem isUnit_of_redRestrict_ne_zero (hdvr : IsDiscreteValuationRing ↥(coeffSubring A K))
    {ϖ' : ↥(coeffSubring A K)} (hirr : Irreducible ϖ') {t : ↥(coeffSubring A K)} (ht : redRestrict red K t ≠ 0) :
    IsUnit t := by
  haveI := hdvr
  by_contra hnu
  apply ht
  rw [redRestrict_eq_zero_iff K red hker hdvr hirr]
  have hmem : t ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  rw [hirr.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨e, he⟩ := hmem
  exact ⟨e, by rw [← he, mul_comm]⟩

private theorem not_isUnit_of_mem_maximalIdeal {t : ↥(coeffSubring A K)} (ht : toA K t ∈ IsLocalRing.maximalIdeal ↥A) :
    ¬ IsUnit t := by
  rw [isUnit_iff_isUnit_toA]
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp ht)

end Coefficients

section NodeRing

variable (red : A →+* k) (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private def evHom : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+*
    ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
  (modularEval (1 * q) (coeffSubring A K)).codRestrict _
    (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))

private theorem evHom_sub_eval_mem (x : ↥(coeffSubring A K)) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    evHom q red a K p - evHom q red a K (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] p)) ∈
      Ideal.span {evHom q red a K (MvPolynomial.X 0 - MvPolynomial.C x), evHom q red a K (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))} := by
  induction p using MvPolynomial.induction_on with
  | C t =>
      rw [MvPolynomial.eval_C, sub_self]
      exact zero_mem _
  | add p r hp hr =>
      rw [map_add, map_add, MvPolynomial.C_add, map_add, add_sub_add_comm]
      exact add_mem hp hr
  | mul_X p i hp =>
      have hgen : evHom q red a K (MvPolynomial.X i) - evHom q red a K (MvPolynomial.C (![x, x ^ q] i)) ∈
          Ideal.span {evHom q red a K (MvPolynomial.X 0 - MvPolynomial.C x), evHom q red a K (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))} := by
        rw [← map_sub]
        fin_cases i
        · exact Ideal.subset_span (Set.mem_insert _ _)
        · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.C_mul, map_mul]
      have hid : evHom q red a K p * evHom q red a K (MvPolynomial.X i)
            - evHom q red a K (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] p)) * evHom q red a K (MvPolynomial.C (![x, x ^ q] i))
          = (evHom q red a K p - evHom q red a K (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] p))) * evHom q red a K (MvPolynomial.X i)
            + evHom q red a K (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] p))
              * (evHom q red a K (MvPolynomial.X i) - evHom q red a K (MvPolynomial.C (![x, x ^ q] i))) := by ring
      rw [hid]
      exact add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hgen)

variable (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) [FiniteDimensional ℚ K]
  (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
  (hdvr : IsDiscreteValuationRing ↥(coeffSubring A K)) {ϖ' : ↥(coeffSubring A K)} (hirr : Irreducible ϖ')

include hker hx hdvr hirr in

private theorem taylor_le_maximalIdeal [CharP k q] [DecidableEq k] [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))] :
    Ideal.span {evHom q red a K (MvPolynomial.X 0 - MvPolynomial.C x), evHom q red a K (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))} ≤
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
  have hm := (ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring (q := q) red a K x hx ϖ'
    (redRestrict_eq_zero_iff K red hker hdvr hirr)).2.2.2
  have hm' : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
      Ideal.span {evHom q red a K (MvPolynomial.C ϖ'), evHom q red a K (MvPolynomial.X 0 - MvPolynomial.C x),
        evHom q red a K (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))} := hm
  rw [hm']
  exact Ideal.span_mono (Set.subset_insert _ _)

include hker hx hdvr hirr in

private theorem isUnit_evHom_of_pointEval_ne_zero [CharP k q] [DecidableEq k]
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    {s : MvPolynomial (Fin 2) ↥(coeffSubring A K)} (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0) :
    IsUnit (evHom q red a K s) := by
  have ht : IsUnit (MvPolynomial.eval ![x, x ^ q] s) :=
    isUnit_of_redRestrict_ne_zero K red hker hdvr hirr (by rw [redRestrict_eval q red a K x hx]; exact hs)
  have htR : IsUnit (evHom q red a K (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] s))) :=
    ht.map ((evHom q red a K).comp MvPolynomial.C)
  have hdiff := taylor_le_maximalIdeal q red a K hker x hx hdvr hirr (evHom_sub_eval_mem q red a K x s)
  by_contra hnu
  have hsm : evHom q red a K s ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  have hCm : evHom q red a K (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] s)) ∈ IsLocalRing.maximalIdeal _ := by
    have h := sub_mem hsm hdiff
    rwa [sub_sub_cancel] at h
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hCm htR)

include hker hx hdvr hirr in

private theorem node_residue_surjective [CharP k q] [DecidableEq k]
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))] :
    Function.Surjective ((IsLocalRing.residue ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))).comp
      ((evHom q red a K).comp MvPolynomial.C)) := by
  intro z
  obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨r, s, hs, hfs⟩ := f.2
  have hfs' : f * evHom q red a K s = evHom q red a K r := Subtype.ext hfs
  have ht : IsUnit (MvPolynomial.eval ![x, x ^ q] s) :=
    isUnit_of_redRestrict_ne_zero K red hker hdvr hirr (by rw [redRestrict_eval q red a K x hx]; exact hs)
  obtain ⟨t', ht'⟩ := ht.exists_right_inv
  set ρ := (IsLocalRing.residue ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))).comp
    ((evHom q red a K).comp MvPolynomial.C) with hρ
  have hcong : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      IsLocalRing.residue _ (evHom q red a K p) = ρ (MvPolynomial.eval ![x, x ^ q] p) := by
    intro p
    have h := taylor_le_maximalIdeal q red a K hker x hx hdvr hirr (evHom_sub_eval_mem q red a K x p)
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h
    rw [hρ, RingHom.comp_apply, RingHom.comp_apply]
    exact h
  refine ⟨MvPolynomial.eval ![x, x ^ q] r * t', ?_⟩
  have h1 : IsLocalRing.residue _ f * ρ (MvPolynomial.eval ![x, x ^ q] s) = ρ (MvPolynomial.eval ![x, x ^ q] r) := by
    rw [← hcong, ← hcong, ← map_mul, hfs']
  have h2 : ρ (MvPolynomial.eval ![x, x ^ q] s) * ρ t' = 1 := by
    rw [← map_mul, ht', map_one]
  calc ρ (MvPolynomial.eval ![x, x ^ q] r * t') = ρ (MvPolynomial.eval ![x, x ^ q] r) * ρ t' := map_mul _ _ _
    _ = IsLocalRing.residue _ f * (ρ (MvPolynomial.eval ![x, x ^ q] s) * ρ t') := by rw [← h1, mul_assoc]
    _ = IsLocalRing.residue _ f := by rw [h2, mul_one]

end NodeRing

end NodeSectionPrime

namespace NodeSectionPrime

open ModularCurve ModularCurve.NodeLocalized

variable (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k]

section Transport

variable {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')

include hKK' in
private theorem coeffSubring_mono : coeffSubring A K ≤ coeffSubring A K' := by
  intro z hz
  exact Subring.mem_inf.mpr ⟨(Subring.mem_inf.mp hz).1, hKK' (Subring.mem_inf.mp hz).2⟩

private def inclCoeff : ↥(coeffSubring A K) →+* ↥(coeffSubring A K') := Subring.inclusion (coeffSubring_mono (A := A) hKK')

private theorem toA_inclCoeff (t : ↥(coeffSubring A K)) : toA K' (inclCoeff (A := A) hKK' t) = toA K t := Subtype.ext rfl

private theorem inclCoeff_ne_zero {t : ↥(coeffSubring A K)} (ht : t ≠ 0) : inclCoeff (A := A) hKK' t ≠ 0 := by
  intro h
  have h2 := congrArg Subtype.val h
  exact ht (Subtype.ext h2)

private theorem isUnit_inclCoeff_iff (t : ↥(coeffSubring A K)) : IsUnit (inclCoeff (A := A) hKK' t) ↔ IsUnit t := by
  rw [isUnit_iff_isUnit_toA, toA_inclCoeff, ← isUnit_iff_isUnit_toA]

variable (red : A →+* k)

private theorem redRestrict_comp_inclCoeff : (redRestrict red K').comp (inclCoeff (A := A) hKK') = redRestrict red K :=
  RingHom.ext fun t => by
    rw [RingHom.comp_apply, redRestrict_apply, redRestrict_apply, toA_inclCoeff]

private theorem constSeries_comp_inclCoeff :
    (CharPReduction.constSeries (coeffSubring A K')).comp (inclCoeff (A := A) hKK') = CharPReduction.constSeries (coeffSubring A K) :=
  RingHom.ext fun _ => rfl

private theorem modularEval_map (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K') (MvPolynomial.map (inclCoeff (A := A) hKK') p) = modularEval (1 * q) (coeffSubring A K) p := by
  unfold modularEval
  rw [MvPolynomial.eval₂Hom_map_hom, constSeries_comp_inclCoeff]

private theorem pointEval_map (a b : k) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    pointEval (coeffSubring A K') (redRestrict red K') a b (MvPolynomial.map (inclCoeff (A := A) hKK') p) =
      pointEval (coeffSubring A K) (redRestrict red K) a b p := by
  unfold pointEval
  rw [MvPolynomial.eval₂Hom_map_hom, redRestrict_comp_inclCoeff]

variable (a : k)

include hKK' in

private theorem node_le_node :
    modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ≤
      modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) := by
  rintro f ⟨r, s, hs, hfs⟩
  refine ⟨MvPolynomial.map (inclCoeff (A := A) hKK') r, MvPolynomial.map (inclCoeff (A := A) hKK') s, ?_, ?_⟩
  · rw [pointEval_map]
    exact hs
  · rw [modularEval_map, modularEval_map]
    exact hfs

private def inclNode : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+*
    ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) :=
  Subring.inclusion (node_le_node q hKK' red a)

private theorem inclNode_evHom (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    inclNode q hKK' red a (evHom q red a K p) = evHom q red a K' (MvPolynomial.map (inclCoeff (A := A) hKK') p) :=
  Subtype.ext (modularEval_map q hKK' p).symm

private theorem inclNode_evHom_C (t : ↥(coeffSubring A K)) :
    inclNode q hKK' red a (evHom q red a K (MvPolynomial.C t)) = evHom q red a K' (MvPolynomial.C (inclCoeff (A := A) hKK' t)) := by
  simp only [inclNode_evHom, MvPolynomial.map_C]

private theorem inclNode_evHom_branch₁ :
    inclNode q hKK' red a (evHom q red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)) =
      evHom q red a K' (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) := by
  simp only [inclNode_evHom, map_sub, map_pow, MvPolynomial.map_X]

private theorem inclNode_evHom_branch₂ :
    inclNode q hKK' red a (evHom q red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) =
      evHom q red a K' (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) := by
  simp only [inclNode_evHom, map_sub, map_pow, MvPolynomial.map_X]

private theorem inclNode_evHom_X_sub_C (i : Fin 2) (t : ↥(coeffSubring A K)) :
    inclNode q hKK' red a (evHom q red a K (MvPolynomial.X i - MvPolynomial.C t)) =
      evHom q red a K' (MvPolynomial.X i - MvPolynomial.C (inclCoeff (A := A) hKK' t)) := by
  simp only [inclNode_evHom, map_sub, MvPolynomial.map_X, MvPolynomial.map_C]

private theorem map_inclNode_span_triple (f g h : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    (Ideal.span {f, g, h}).map (inclNode q hKK' red a) =
      Ideal.span {inclNode q hKK' red a f, inclNode q hKK' red a g, inclNode q hKK' red a h} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_pair]

private theorem map_inclNode_span_pair (f g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    (Ideal.span {f, g}).map (inclNode q hKK' red a) = Ideal.span {inclNode q hKK' red a f, inclNode q hKK' red a g} := by
  rw [Ideal.map_span, Set.image_pair]

end Transport

private theorem span_pair_congr_of_mem {R : Type*} [CommRing R] {π p g h : R} (hp : p ∈ Ideal.span {π})
    (heq : Ideal.span {p, g} = Ideal.span {p, h}) : Ideal.span {π, g} = Ideal.span {π, h} := by
  have key : ∀ z : R, Ideal.span {π, z} = Ideal.span {π} ⊔ Ideal.span {p, z} := by
    intro z
    rw [Ideal.span_insert π, Ideal.span_insert p, ← sup_assoc,
      sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hp)]
  rw [key, key, heq]

end NodeSectionPrime

namespace NodeSectionPrime

open ModularCurve ModularCurve.NodeLocalized

variable (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k]

section NormalModel

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem constSeries_mem_fieldOver (t : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) t ∈ fieldOver (1 * q) K :=
  Subfield.subset_closure (Or.inl ⟨⟨(t : AlgebraicClosure ℚ), coe_mem_field K t⟩, rfl⟩)

private theorem jqModC_mem_fieldOver' : jqModC (AlgebraicClosure ℚ) ∈ fieldOver (1 * q) K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

private theorem jqNModC_mem_fieldOver' : jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ fieldOver (1 * q) K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private theorem constSeries_mem_jRing (t : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) t ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨t, rfl⟩)

private theorem mem_jIntegralClosure_of_mem_jRing {z : LaurentSeries (AlgebraicClosure ℚ)} (hzF : z ∈ fieldOver (1 * q) K)
    (hz : z ∈ jRing A K) : z ∈ jIntegralClosure (1 * q) A K := by
  refine ⟨hzF, ?_⟩
  have h : IsIntegral ↥(jRing A K) (algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) ⟨z, hz⟩) := isIntegral_algebraMap
  exact h

private theorem constSeries_mem_jIntegralClosure (t : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) t ∈ jIntegralClosure (1 * q) A K :=
  mem_jIntegralClosure_of_mem_jRing q K (constSeries_mem_fieldOver q K t) (constSeries_mem_jRing K t)

private theorem modularEval_mem_jIntegralClosure (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ jIntegralClosure (1 * q) A K := by
  induction p using MvPolynomial.induction_on with
  | C t =>
      rw [modularEval, MvPolynomial.eval₂Hom_C]
      exact constSeries_mem_jIntegralClosure q K t
  | add p r hp hr =>
      rw [map_add]
      exact add_mem hp hr
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [modularEval, MvPolynomial.eval₂Hom_X']
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · exact (ModularCurve.NodeLocalized.jqModC_mem_jIntegralClosure_and_jqNModC_mem A K).1
      · exact (ModularCurve.NodeLocalized.jqModC_mem_jIntegralClosure_and_jqNModC_mem A K).2

private theorem modularEval_mem_fieldOver' (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ fieldOver (1 * q) K := by
  induction p using MvPolynomial.induction_on with
  | C t =>
      rw [modularEval, MvPolynomial.eval₂Hom_C]
      exact constSeries_mem_fieldOver q K t
  | add p r hp hr =>
      rw [map_add]
      exact add_mem hp hr
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [modularEval, MvPolynomial.eval₂Hom_X']
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · exact jqModC_mem_fieldOver' q K
      · exact jqNModC_mem_fieldOver' q K

private theorem jRing_le_node (red : A →+* k) (a : k) :
    jRing A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  refine Subring.closure_le.mpr ?_
  rintro z (⟨t, rfl⟩ | hz)
  · have h := modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C t)
    rwa [modularEval, MvPolynomial.eval₂Hom_C] at h
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h := modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0)
    rwa [modularEval, MvPolynomial.eval₂Hom_X'] at h

variable (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (a : k) [FiniteDimensional ℚ K]
  (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
  (hdvr : IsDiscreteValuationRing ↥(coeffSubring A K)) {ϖ' : ↥(coeffSubring A K)} (hirr : Irreducible ϖ')

include hker hx hdvr hirr in

private theorem node_le_fieldOver [CharP k q] [DecidableEq k]
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    {f : LaurentSeries (AlgebraicClosure ℚ)}
    (hf : f ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) : f ∈ fieldOver (1 * q) K := by
  obtain ⟨r, s, hs, hfs⟩ := hf
  have hsu : IsUnit (evHom q red a K s) := isUnit_evHom_of_pointEval_ne_zero q red a K hker x hx hdvr hirr hs
  have hs0 : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := by
    intro h0
    have h0' : evHom q red a K s = 0 := Subtype.ext h0
    rw [h0'] at hsu
    exact not_isUnit_zero hsu
  have hf' : f = modularEval (1 * q) (coeffSubring A K) r * (modularEval (1 * q) (coeffSubring A K) s)⁻¹ := by
    rw [← hfs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hf']
  exact mul_mem (modularEval_mem_fieldOver' q K r) (inv_mem (modularEval_mem_fieldOver' q K s))

include hker hx hdvr hirr in

private theorem jIntegralClosure_le_node [CharP k q] [DecidableEq k]
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    (hic : IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    jIntegralClosure (1 * q) A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by

  let toF : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+* ↥(fieldOver (1 * q) K) :=
    { toFun := fun f => ⟨(f : LaurentSeries (AlgebraicClosure ℚ)), node_le_fieldOver q K red hker a x hx hdvr hirr f.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  letI : Algebra ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ↥(fieldOver (1 * q) K) :=
    toF.toAlgebra
  haveI hfr : IsFractionRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
      ↥(fieldOver (1 * q) K) := by
    refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · intro y
      apply isUnit_iff_ne_zero.mpr
      intro hy
      have h0 := congrArg Subtype.val hy
      exact nonZeroDivisors.coe_ne_zero y (Subtype.ext h0)
    · intro z
      obtain ⟨y, w, hy, hw, hw0, hz⟩ := ModularCurve.NodeLocalized.exists_mul_eq_of_mem_fieldOver red a K z.2
      have hw0' : (⟨w, hw⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ≠ 0 := by
        intro h
        apply hw0
        have h2 := congrArg Subtype.val h
        exact h2
      exact ⟨(⟨y, hy⟩, ⟨⟨w, hw⟩, mem_nonZeroDivisors_of_ne_zero hw0'⟩), Subtype.ext hz⟩
    · intro f g hfg
      have h := congrArg Subtype.val hfg
      have hfg' : f = g := Subtype.ext (by exact h)
      exact ⟨1, by rw [hfg']⟩
  haveI := hic

  letI : Algebra ↥(jRing A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    (Subring.inclusion (jRing_le_node q K red a)).toAlgebra
  haveI : IsScalarTower ↥(jRing A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
      (LaurentSeries (AlgebraicClosure ℚ)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ↥(fieldOver (1 * q) K)
      (LaurentSeries (AlgebraicClosure ℚ)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rintro z ⟨hzF, hzI⟩
  have hzR : IsIntegral ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) z := hzI.tower_top
  have hzF' : IsIntegral ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
      (⟨z, hzF⟩ : ↥(fieldOver (1 * q) K)) := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
      ↥(fieldOver (1 * q) K) (LaurentSeries (AlgebraicClosure ℚ))) (fun _ _ h => Subtype.ext h)).mp ?_
    exact hzR
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff
    (R := ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) (K := ↥(fieldOver (1 * q) K))).mp hzF'
  have hy₁ := congrArg Subtype.val hy
  have hy₂ : ((y : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
      LaurentSeries (AlgebraicClosure ℚ)) = z := hy₁
  rw [← hy₂]
  exact y.2

include hker hx hdvr hirr in

private theorem isLocalization_node [CharP k q] [DecidableEq k]
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    (hle : jIntegralClosure (1 * q) A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :
    letI : Algebra ↥(jIntegralClosure (1 * q) A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
      (Subring.inclusion hle).toAlgebra
    IsLocalization ((IsUnit.submonoid ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))).comap
        (Subring.inclusion hle))
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
  letI : Algebra ↥(jIntegralClosure (1 * q) A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    (Subring.inclusion hle).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · intro y
    exact (IsUnit.mem_submonoid_iff _).mp (Submonoid.mem_comap.mp y.2)
  · intro f
    obtain ⟨r, s, hs, hfs⟩ := f.2
    have hsu : IsUnit (evHom q red a K s) := isUnit_evHom_of_pointEval_ne_zero q red a K hker x hx hdvr hirr hs
    refine ⟨(⟨modularEval (1 * q) (coeffSubring A K) r, modularEval_mem_jIntegralClosure q K r⟩,
      ⟨⟨modularEval (1 * q) (coeffSubring A K) s, modularEval_mem_jIntegralClosure q K s⟩, ?_⟩), ?_⟩
    · exact Submonoid.mem_comap.mpr ((IsUnit.mem_submonoid_iff _).mpr hsu)
    · exact Subtype.ext hfs
  · intro f g hfg
    have h := congrArg Subtype.val hfg
    have hfg' : f = g := Subtype.ext (by exact h)
    exact ⟨1, by rw [hfg']⟩

end NormalModel

end NodeSectionPrime

namespace CrossingSectionPrime

private theorem pow_mul_notMem {R : Type*} [CommRing R] {J : Ideal R} (hJ : J.IsPrime) {π η ε : R} (hπ : π ∉ J)
    (hη : IsUnit η) (hε : IsUnit ε) (e f : ℕ) : (η * π ^ e) ^ f * ε ∉ J := by
  intro h
  rcases hJ.mem_or_mem h with h1 | h1
  · have h2 : η * π ^ e ∈ J := hJ.mem_of_pow_mem _ h1
    rcases hJ.mem_or_mem h2 with h3 | h3
    · exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h3 hη)
    · exact hπ (hJ.mem_of_pow_mem _ h3)
  · exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 hε)

private theorem mul_mul_notMem {R : Type*} [CommRing R] {J : Ideal R} (hJ : J.IsPrime) {u s s' : R} (hu : u ∉ J)
    (hs : IsUnit s) (hs' : IsUnit s') : u * s * s' ∉ J := by
  intro h
  rcases hJ.mem_or_mem h with h1 | h1
  · rcases hJ.mem_or_mem h1 with h2 | h2
    · exact hu h2
    · exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hs)
  · exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 hs')

end CrossingSectionPrime

namespace NodeSectionPrime

open ModularCurve ModularCurve.NodeLocalized

variable (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k]

section Exponents

variable {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')

private def valueElt (c : ↥A) (hcK' : (c : AlgebraicClosure ℚ) ∈ K') : ↥(coeffSubring A K') :=
  ⟨(c : AlgebraicClosure ℚ), Subring.mem_inf.mpr ⟨c.2, hcK'⟩⟩

private theorem toA_valueElt (c : ↥A) (hcK' : (c : AlgebraicClosure ℚ) ∈ K') : toA K' (valueElt (A := A) c hcK') = c :=
  Subtype.ext rfl

variable (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

include hKK' hker in

private theorem exists_exponents [CharP k q] (hdvr : IsDiscreteValuationRing ↥(coeffSubring A K'))
    {ϖ' : ↥(coeffSubring A K')} (hirr : Irreducible ϖ')
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε) (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε) (d : ℕ)
    (c : ↥A) (hc : c ∈ IsLocalRing.maximalIdeal A) (hadm : ∃ m, m ∈ IsLocalRing.maximalIdeal A ∧ c * m = ((q : ℕ) : ↥A) ^ d)
    (hcK' : (c : AlgebraicClosure ℚ) ∈ K') :
    ∃ (e₁ ae : ℕ) (η cu : (↥(coeffSubring A K'))ˣ),
      inclCoeff (A := A) hKK' ϖ = ↑η * ϖ' ^ e₁ ∧ 1 ≤ e₁ ∧ valueElt (A := A) c hcK' = ↑cu * ϖ' ^ ae ∧ 1 ≤ ae ∧ ae < e₁ * (d * eK) := by
  haveI := hdvr
  obtain ⟨m, hm, hcm⟩ := hadm
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hqd : ((q : ℕ) : AlgebraicClosure ℚ) ^ d ≠ 0 := pow_ne_zero d hq0

  have hcm' : (c : AlgebraicClosure ℚ) * (m : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) ^ d := by
    have h := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hcm
    simpa using h
  have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hcm'
    exact hqd hcm'.symm
  have hm0 : (m : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcm'
    exact hqd hcm'.symm

  have hmK' : (m : AlgebraicClosure ℚ) ∈ K' := by
    have hmeq : (m : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ)⁻¹ * ((q : ℕ) : AlgebraicClosure ℚ) ^ d := by
      rw [← hcm', ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rw [hmeq]
    exact K'.mul_mem (K'.inv_mem hcK') (pow_mem (natCast_mem K' q) d)

  have hϖred : red (toA K ϖ) = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  have hϖnu : ¬ IsUnit ϖ := not_isUnit_of_mem_maximalIdeal K ((hker _).mp hϖred)
  have hϖ0 : ϖ ≠ 0 := by
    have hqred : redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) = 0 := by
      rw [map_natCast, CharP.cast_eq_zero]
    obtain ⟨d₀, hd₀⟩ := (hϖ _).mp hqred
    intro h
    rw [h, zero_mul] at hd₀
    apply hq0
    simpa using congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hd₀
  obtain ⟨e₁, η, hη⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (inclCoeff_ne_zero hKK' hϖ0) hirr
  have he₁ : 1 ≤ e₁ := by
    rcases Nat.eq_zero_or_pos e₁ with h | h
    · exfalso
      apply hϖnu
      rw [← isUnit_inclCoeff_iff hKK', hη, h, pow_zero, mul_one]
      exact η.isUnit
    · exact h

  set cO : ↥(coeffSubring A K') := valueElt (A := A) c hcK' with hcOdef
  set mO : ↥(coeffSubring A K') := ⟨(m : AlgebraicClosure ℚ), Subring.mem_inf.mpr ⟨m.2, hmK'⟩⟩ with hmOdef
  have hcO0 : cO ≠ 0 := by
    intro h
    apply hc0
    have h2 := congrArg Subtype.val h
    exact h2
  have hmO0 : mO ≠ 0 := by
    intro h
    apply hm0
    have h2 := congrArg Subtype.val h
    exact h2
  have hcOnu : ¬ IsUnit cO := not_isUnit_of_mem_maximalIdeal K' (by rw [hcOdef, toA_valueElt]; exact hc)
  have hmOnu : ¬ IsUnit mO := not_isUnit_of_mem_maximalIdeal K' (by
    have h : toA K' mO = m := Subtype.ext rfl
    rw [h]; exact hm)
  have hcmO : cO * mO = ((q : ℕ) : ↥(coeffSubring A K')) ^ d := by
    apply Subtype.ext
    push_cast
    exact hcm'
  have hqO : ((q : ℕ) : ↥(coeffSubring A K')) = inclCoeff (A := A) hKK' ϖ ^ eK * inclCoeff (A := A) hKK' ε := by
    rw [← map_natCast (inclCoeff (A := A) hKK'), hqϖ, map_mul, map_pow]
  have hε' : IsUnit (inclCoeff (A := A) hKK' ε) := (isUnit_inclCoeff_iff hKK' ε).mpr hε
  obtain ⟨ae, cu, hcu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hcO0 hirr
  obtain ⟨be, mu, hmu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hmO0 hirr
  have hae : 1 ≤ ae := by
    rcases Nat.eq_zero_or_pos ae with h | h
    · exfalso
      apply hcOnu
      rw [hcu, h, pow_zero, mul_one]
      exact cu.isUnit
    · exact h
  have hbe : 1 ≤ be := by
    rcases Nat.eq_zero_or_pos be with h | h
    · exfalso
      apply hmOnu
      rw [hmu, h, pow_zero, mul_one]
      exact mu.isUnit
    · exact h

  have key : (↑cu : ↥(coeffSubring A K')) * ↑mu * ϖ' ^ (ae + be) =
      (↑η : ↥(coeffSubring A K')) ^ (eK * d) * inclCoeff (A := A) hKK' ε ^ d * ϖ' ^ (e₁ * eK * d) := by
    have h := hcmO
    rw [hcu, hmu, hqO, hη] at h
    linear_combination h
  have key' : ((cu * mu : (↥(coeffSubring A K'))ˣ) : ↥(coeffSubring A K')) * ϖ' ^ (ae + be) =
      ((η ^ (eK * d) * hε'.unit ^ d : (↥(coeffSubring A K'))ˣ) : ↥(coeffSubring A K')) * ϖ' ^ (e₁ * eK * d) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    exact key
  have hab : ae + be = e₁ * eK * d := IsDiscreteValuationRing.unit_mul_pow_congr_pow hirr hirr _ _ _ _ key'
  refine ⟨e₁, ae, η, cu, hη, he₁, hcu, hae, ?_⟩
  have hn : e₁ * (d * eK) = ae + be := by rw [hab]; ring
  rw [hn]
  omega

end Exponents

end NodeSectionPrime

namespace NodeSectionPrime

open ModularCurve ModularCurve.NodeLocalized

variable (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k]

section Branches

variable {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') (red : A →+* k) (a : k)

private theorem branch_primes [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K'] (ha2 : a ^ (q ^ 2) = a)
    (ϖ' : ↥(coeffSubring A K')) (hϖ' : ∀ c : ↥(coeffSubring A K'), redRestrict red K' c = 0 ↔ ∃ d, c = ϖ' * d)
    (ϖ : ↥(coeffSubring A K)) (hπ₁ : evHom q red a K' (MvPolynomial.C (inclCoeff (A := A) hKK' ϖ)) ∈ Ideal.span {evHom q red a K' (MvPolynomial.C ϖ')})
    (G' H' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hsp1 : Ideal.span {evHom q red a K (MvPolynomial.C ϖ), G'} =
      Ideal.span {evHom q red a K (MvPolynomial.C ϖ), evHom q red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)})
    (hsp2 : Ideal.span {evHom q red a K (MvPolynomial.C ϖ), H'} =
      Ideal.span {evHom q red a K (MvPolynomial.C ϖ), evHom q red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)}) :
    (Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a G'}).IsPrime ∧
    (Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a H'}).IsPrime ∧
    inclNode q hKK' red a G' ∉ Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a H'} ∧
    inclNode q hKK' red a H' ∉ Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a G'} := by
  obtain ⟨⟨hP1, hnot1, -⟩, hP2'⟩ :=
    ModularCurve.NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint (q := q) red a K' ϖ' hϖ'
  obtain ⟨hP2, hnot2⟩ := hP2' ha2
  have hP1' : (Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), evHom q red a K' (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)}).IsPrime := hP1
  have hnot1' : evHom q red a K' (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) ∉
      Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), evHom q red a K' (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} := hnot1
  have hP2'' : (Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), evHom q red a K' (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)}).IsPrime := hP2
  have hnot2' : evHom q red a K' (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) ∉
      Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), evHom q red a K' (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)} := hnot2

  have h1 := congrArg (Ideal.map (inclNode q hKK' red a)) hsp1
  rw [map_inclNode_span_pair, map_inclNode_span_pair, inclNode_evHom_C, inclNode_evHom_branch₁] at h1
  have h2 := congrArg (Ideal.map (inclNode q hKK' red a)) hsp2
  rw [map_inclNode_span_pair, map_inclNode_span_pair, inclNode_evHom_C, inclNode_evHom_branch₂] at h2
  have hQeq := span_pair_congr_of_mem hπ₁ h1
  have hQ'eq := span_pair_congr_of_mem hπ₁ h2
  have hQ : (Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a G'}).IsPrime := by
    rw [hQeq]; exact hP1'
  have hQ' : (Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a H'}).IsPrime := by
    rw [hQ'eq]; exact hP2''
  refine ⟨hQ, hQ', ?_, ?_⟩
  · intro hu
    apply hnot2'
    rw [← hQ'eq]
    have hle : Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a G'} ≤
        Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a H'} := by
      rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Ideal.subset_span (Set.mem_insert _ _), hu⟩
    exact hle (by rw [hQeq]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  · intro hv
    apply hnot1'
    rw [← hQeq]
    have hle : Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a H'} ≤
        Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a G'} := by
      rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Ideal.subset_span (Set.mem_insert _ _), hv⟩
    exact hle (by rw [hQ'eq]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

private theorem maximalIdeal_eq_span
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))]
    (x : ↥(coeffSubring A K)) (ϖ : ↥(coeffSubring A K)) (ϖ' : ↥(coeffSubring A K'))
    (G' H' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hmK : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
      Ideal.span {evHom q red a K (MvPolynomial.C ϖ), evHom q red a K (MvPolynomial.X 0 - MvPolynomial.C x),
        evHom q red a K (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))})
    (hmax : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
      Ideal.span {evHom q red a K (MvPolynomial.C ϖ), G', H'})
    (hmK' : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) =
      Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), evHom q red a K' (MvPolynomial.X 0 - MvPolynomial.C (inclCoeff (A := A) hKK' x)),
        evHom q red a K' (MvPolynomial.X 1 - MvPolynomial.C (inclCoeff (A := A) hKK' x ^ q))})
    (hπ₁ : evHom q red a K' (MvPolynomial.C (inclCoeff (A := A) hKK' ϖ)) ∈ Ideal.span {evHom q red a K' (MvPolynomial.C ϖ')})
    (hQ : (Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a G'}).IsPrime)
    (hQ' : (Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a H'}).IsPrime) :
    IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) =
      Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a G', inclNode q hKK' red a H'} := by

  have hgen : ∀ z ∈ Ideal.span {evHom q red a K (MvPolynomial.C ϖ), evHom q red a K (MvPolynomial.X 0 - MvPolynomial.C x),
      evHom q red a K (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))},
      inclNode q hKK' red a z ∈ Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a G', inclNode q hKK' red a H'} := by
    intro z hz
    rw [← hmK, hmax] at hz
    have h := Ideal.mem_map_of_mem (inclNode q hKK' red a) hz
    rw [map_inclNode_span_triple, inclNode_evHom_C] at h
    refine Ideal.span_le.mpr ?_ h
    rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)),
      Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))⟩
    have h1 : evHom q red a K' (MvPolynomial.C (inclCoeff (A := A) hKK' ϖ)) ∈
        Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), inclNode q hKK' red a G', inclNode q hKK' red a H'} :=
      Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hπ₁
    exact h1
  apply le_antisymm
  · rw [hmK', Ideal.span_le, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Ideal.subset_span (Set.mem_insert _ _), ?_, ?_⟩
    · rw [← inclNode_evHom_X_sub_C]
      exact hgen _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    · rw [← map_pow, ← inclNode_evHom_X_sub_C]
      exact hgen _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [hmK']
      exact Ideal.subset_span (Set.mem_insert _ _)
    · exact IsLocalRing.le_maximalIdeal hQ.ne_top (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    · exact IsLocalRing.le_maximalIdeal hQ'.ne_top (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

end Branches

section Elements

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private def evC (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : ↥(jIntegralClosure (1 * q) A K) :=
  ⟨modularEval (1 * q) (coeffSubring A K) p, modularEval_mem_jIntegralClosure q K p⟩

private def constC (t : ↥(coeffSubring A K)) : ↥(jIntegralClosure (1 * q) A K) :=
  ⟨CharPReduction.constSeries (coeffSubring A K) t, constSeries_mem_jIntegralClosure q K t⟩

variable (red : A →+* k) (a : k)
  (hle : jIntegralClosure (1 * q) A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))

private theorem inclusion_evC (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    Subring.inclusion hle (evC q K p) = evHom q red a K p := Subtype.ext rfl

private theorem inclusion_constC (t : ↥(coeffSubring A K)) :
    Subring.inclusion hle (constC q K t) = evHom q red a K (MvPolynomial.C t) := by
  apply Subtype.ext
  show CharPReduction.constSeries (coeffSubring A K) t = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C t)
  rw [modularEval, MvPolynomial.eval₂Hom_C]

end Elements

section Presentation

variable {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') (red : A →+* k) (a : k)
  (G' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
  (rG sG : MvPolynomial (Fin 2) ↥(coeffSubring A K))
  (hGs : (G' : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) sG = modularEval (1 * q) (coeffSubring A K) rG)

include hGs in

private theorem inclusion_evC_map (hle : jIntegralClosure (1 * q) A K' ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) :
    Subring.inclusion hle (evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') rG)) = inclNode q hKK' red a G' * Subring.inclusion hle (evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG)) := by
  apply Subtype.ext
  show modularEval (1 * q) (coeffSubring A K') (MvPolynomial.map (inclCoeff (A := A) hKK') rG) =
    (G' : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K') (MvPolynomial.map (inclCoeff (A := A) hKK') sG)
  rw [modularEval_map, modularEval_map]
  exact hGs.symm

include hGs in

private theorem coe_mul_evC_map :
    (G' : LaurentSeries (AlgebraicClosure ℚ)) * ((evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG) : ↥(jIntegralClosure (1 * q) A K')) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') rG) : ↥(jIntegralClosure (1 * q) A K')) : LaurentSeries (AlgebraicClosure ℚ)) := by
  show (G' : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K') (MvPolynomial.map (inclCoeff (A := A) hKK') sG) =
    modularEval (1 * q) (coeffSubring A K') (MvPolynomial.map (inclCoeff (A := A) hKK') rG)
  rw [modularEval_map, modularEval_map]
  exact hGs

include hGs in

private theorem coe_sub_mul_evC_map (c : ↥A) (hcK' : (c : AlgebraicClosure ℚ) ∈ K') :
    ((G' : LaurentSeries (AlgebraicClosure ℚ)) - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ))
        * ((evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG) : ↥(jIntegralClosure (1 * q) A K')) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') rG) - constC q K' (valueElt (A := A) c hcK') * evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG) : ↥(jIntegralClosure (1 * q) A K')) :
        LaurentSeries (AlgebraicClosure ℚ)) := by
  show ((G' : LaurentSeries (AlgebraicClosure ℚ)) - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ))
      * modularEval (1 * q) (coeffSubring A K') (MvPolynomial.map (inclCoeff (A := A) hKK') sG) =
    modularEval (1 * q) (coeffSubring A K') (MvPolynomial.map (inclCoeff (A := A) hKK') rG)
      - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)
        * modularEval (1 * q) (coeffSubring A K') (MvPolynomial.map (inclCoeff (A := A) hKK') sG)
  rw [modularEval_map, modularEval_map, sub_mul, hGs]

end Presentation

section Conjuncts

private theorem conjuncts (red : A →+* k) (a : k) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    (G' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hGF : (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K')
    (c : ↥A) (hcK' : (c : AlgebraicClosure ℚ) ∈ K')
    (hunit : ∀ t : MvPolynomial (Fin 2) ↥(coeffSubring A K'),
      pointEval (coeffSubring A K') (redRestrict red K') a (a ^ q) t ≠ 0 → IsUnit (evHom q red a K' t))
    (hle : jIntegralClosure (1 * q) A K' ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))
    (J : Ideal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))) (hJ : J.IsPrime)
    (hJ1 : (Ideal.comap (Subring.inclusion hle) J).height = 1)
    (hqJ : ((q : ℕ) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))) ∉ J)
    (huJ : inclNode q hKK' red a G' ∉ J)
    (hgJ : inclNode q hKK' red a G' - evHom q red a K' (MvPolynomial.C (valueElt (A := A) c hcK')) ∈ J)
    (hg0 : inclNode q hKK' red a G' - evHom q red a K' (MvPolynomial.C (valueElt (A := A) c hcK')) ≠ 0)
    (hgen : ∀ t ∈ J, ∃ α : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)), t * inclNode q hKK' red a G' = (inclNode q hKK' red a G' - evHom q red a K' (MvPolynomial.C (valueElt (A := A) c hcK'))) * α) :
    (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' ∧
    ∃ (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K')), 𝔭.IsPrime ∧ 𝔭.height = 1 ∧
      ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K')) ∉ 𝔭 ∧
      (∀ s : MvPolynomial (Fin 2) ↥(coeffSubring A K'),
        pointEval (coeffSubring A K') (redRestrict red K') a (a ^ q) s ≠ 0 →
          ∀ hs : modularEval (1 * q) (coeffSubring A K') s ∈ jIntegralClosure (1 * q) A K',
            (⟨_, hs⟩ : ↥(jIntegralClosure (1 * q) A K')) ∉ 𝔭) ∧
      ∃ r₀ r s : ↥(jIntegralClosure (1 * q) A K'), s ∉ 𝔭 ∧ r ∈ 𝔭 ∧
        (G' : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) = r₀ ∧
        ((G' : LaurentSeries (AlgebraicClosure ℚ))
            - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ))
          * (s : LaurentSeries (AlgebraicClosure ℚ)) = r ∧
        r ≠ 0 ∧ ∀ t ∈ 𝔭, ∃ u v : ↥(jIntegralClosure (1 * q) A K'), v ∉ 𝔭 ∧ t * v = r * u := by
  obtain ⟨rG, sG, hsG, hGs⟩ := G'.2
  have hsu : IsUnit (evHom q red a K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG)) := hunit _ (by rw [pointEval_map]; exact hsG)
  have hsR := inclusion_evC q K' red a hle (MvPolynomial.map (inclCoeff (A := A) hKK') sG)
  have hr₀R := inclusion_evC_map q hKK' red a G' rG sG hGs hle
  have hcR := inclusion_constC q K' red a hle (valueElt (A := A) c hcK')
  have hrR : Subring.inclusion hle (evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') rG) - constC q K' (valueElt (A := A) c hcK') * evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG)) =
      (inclNode q hKK' red a G' - evHom q red a K' (MvPolynomial.C (valueElt (A := A) c hcK'))) * Subring.inclusion hle (evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG)) := by
    rw [map_sub (Subring.inclusion hle), map_mul (Subring.inclusion hle), hr₀R, hcR, sub_mul]
  haveI := hJ
  refine ⟨hGF, Ideal.comap (Subring.inclusion hle) J, Ideal.comap_isPrime (Subring.inclusion hle) J, hJ1, ?_, ?_,
    evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') rG), evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') rG) - constC q K' (valueElt (A := A) c hcK') * evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG), evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG),
    ?_, ?_, coe_mul_evC_map q hKK' red a G' rG sG hGs, coe_sub_mul_evC_map q hKK' red a G' rG sG hGs c hcK', ?_, ?_⟩
  ·
    intro hmem
    have h1 := Ideal.mem_comap.mp hmem
    rw [map_natCast (Subring.inclusion hle)] at h1
    exact hqJ h1
  ·
    intro t ht hts hmem
    have h1 := Ideal.mem_comap.mp hmem
    have h2 : evHom q red a K' t ∈ J := h1
    exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 (hunit t ht))
  ·
    intro hmem
    have h1 := Ideal.mem_comap.mp hmem
    rw [hsR] at h1
    exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 hsu)
  ·
    apply Ideal.mem_comap.mpr
    rw [hrR]
    exact Ideal.mul_mem_right _ _ hgJ
  ·
    intro hr0
    have h1 := congrArg (Subring.inclusion hle) hr0
    rw [map_zero (Subring.inclusion hle), hrR] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hg0 h2
    · rw [hsR] at h2
      exact hsu.ne_zero h2
  ·
    intro t ht
    obtain ⟨α, hα⟩ := hgen _ (Ideal.mem_comap.mp ht)
    obtain ⟨rα, sα, hsα, hαs⟩ := α.2
    have hsαR := inclusion_evC q K' red a hle sα
    have hyαR : α * Subring.inclusion hle (evC q K' sα) = Subring.inclusion hle (evC q K' rα) := Subtype.ext hαs
    refine ⟨evC q K' rα, evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') rG) * evC q K' sα, ?_, ?_⟩
    · intro hmem
      have h2 := Ideal.mem_comap.mp hmem
      rw [map_mul (Subring.inclusion hle), hr₀R, hsαR, hsR] at h2
      exact CrossingSectionPrime.mul_mul_notMem hJ huJ hsu (hunit sα hsα) h2
    · apply Subring.inclusion_injective hle
      rw [map_mul (Subring.inclusion hle), map_mul (Subring.inclusion hle), map_mul (Subring.inclusion hle), hr₀R, hrR, ← hyαR]
      linear_combination (Subring.inclusion hle (evC q K' (MvPolynomial.map (inclCoeff (A := A) hKK') sG)) * Subring.inclusion hle (evC q K' sα)) * hα

end Conjuncts

end NodeSectionPrime

namespace NodeSectionPrime

open ModularCurve ModularCurve.NodeLocalized

private theorem main
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hw : IsUnit w) (d : ℕ)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (d * eK) * w)
    (hmax : ∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))})
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (c : A) (hc : c ∈ IsLocalRing.maximalIdeal A)
    (hadm : ∃ m, m ∈ IsLocalRing.maximalIdeal A ∧ c * m = ((q : ℕ) : A) ^ d)
    (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K'] (hKK' : K ≤ K')
    (hcK' : (c : AlgebraicClosure ℚ) ∈ K') :
    (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' ∧
    ∃ (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K')), 𝔭.IsPrime ∧ 𝔭.height = 1 ∧
      ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K')) ∉ 𝔭 ∧
      (∀ s : MvPolynomial (Fin 2) ↥(coeffSubring A K'),
        pointEval (coeffSubring A K') (redRestrict red K') a (a ^ q) s ≠ 0 →
          ∀ hs : modularEval (1 * q) (coeffSubring A K') s ∈ jIntegralClosure (1 * q) A K',
            (⟨_, hs⟩ : ↥(jIntegralClosure (1 * q) A K')) ∉ 𝔭) ∧
      ∃ r₀ r s : ↥(jIntegralClosure (1 * q) A K'), s ∉ 𝔭 ∧ r ∈ 𝔭 ∧
        (G' : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) = r₀ ∧
        ((G' : LaurentSeries (AlgebraicClosure ℚ))
            - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ))
          * (s : LaurentSeries (AlgebraicClosure ℚ)) = r ∧
        r ≠ 0 ∧ ∀ t ∈ 𝔭, ∃ u v : ↥(jIntegralClosure (1 * q) A K'), v ∉ 𝔭 ∧ t * v = r * u := by

  have hdvr : IsDiscreteValuationRing ↥(coeffSubring A K') := isDiscreteValuationRing_coeffSubring q K' red hker
  haveI := hdvr
  obtain ⟨ϖ', hirr⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K')
  have hϖ' : ∀ t : ↥(coeffSubring A K'), redRestrict red K' t = 0 ↔ ∃ e, t = ϖ' * e :=
    redRestrict_eq_zero_iff K' red hker hdvr hirr
  have hx' : redRestrict red K' (inclCoeff (A := A) hKK' x) = a :=
    (RingHom.congr_fun (redRestrict_comp_inclCoeff hKK' red) x).trans hx

  have hK := ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring (q := q) red a K x hx ϖ hϖ
  have hK' := ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring (q := q) red a K'
    (inclCoeff (A := A) hKK' x) hx' ϖ' hϖ'
  haveI hlocK : IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := hK.2.1
  haveI hnoethK' : IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) := hK'.1
  haveI hlocK' : IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) := hK'.2.1
  have hdim : ringKrullDim ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) = 2 := hK'.2.2.1
  have hmK : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
      Ideal.span {evHom q red a K (MvPolynomial.C ϖ), evHom q red a K (MvPolynomial.X 0 - MvPolynomial.C x),
        evHom q red a K (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))} := hK.2.2.2
  have hmK' : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) =
      Ideal.span {evHom q red a K' (MvPolynomial.C ϖ'), evHom q red a K' (MvPolynomial.X 0 - MvPolynomial.C (inclCoeff (A := A) hKK' x)),
        evHom q red a K' (MvPolynomial.X 1 - MvPolynomial.C (inclCoeff (A := A) hKK' x ^ q))} := hK'.2.2.2
  have hmax' : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
      Ideal.span {evHom q red a K (MvPolynomial.C ϖ), G', H'} := hmax
  have hGH₀ : G' * H' = evHom q red a K (MvPolynomial.C ϖ) ^ (d * eK) * w := hGH

  obtain ⟨e₁, ae, η, cu, hη, he₁, hcu, hae, han⟩ :=
    exists_exponents q hKK' red hker hdvr hirr ϖ hϖ eK ε hε hqϖ d c hc hadm hcK'
  have hϖ₁ : evHom q red a K' (MvPolynomial.C (inclCoeff (A := A) hKK' ϖ)) =
      evHom q red a K' (MvPolynomial.C (η : ↥(coeffSubring A K'))) * evHom q red a K' (MvPolynomial.C ϖ') ^ e₁ := by
    rw [hη, MvPolynomial.C_mul, MvPolynomial.C_pow, map_mul (evHom q red a K'), map_pow (evHom q red a K')]
  have hπ₁ : evHom q red a K' (MvPolynomial.C (inclCoeff (A := A) hKK' ϖ)) ∈ Ideal.span {evHom q red a K' (MvPolynomial.C ϖ')} := by
    rw [hϖ₁]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by omega))
  have hηu : IsUnit (evHom q red a K' (MvPolynomial.C (η : ↥(coeffSubring A K')))) :=
    η.isUnit.map ((evHom q red a K').comp MvPolynomial.C)
  have hεu : IsUnit (evHom q red a K' (MvPolynomial.C (inclCoeff (A := A) hKK' ε))) :=
    ((isUnit_inclCoeff_iff hKK' ε).mpr hε).map ((evHom q red a K').comp MvPolynomial.C)
  have hc₀R : IsUnit (evHom q red a K' (MvPolynomial.C (cu : ↥(coeffSubring A K')))) :=
    cu.isUnit.map ((evHom q red a K').comp MvPolynomial.C)

  obtain ⟨hQ, hQ', huQ', hvQ⟩ := branch_primes q hKK' red a ha2 ϖ' hϖ' ϖ hπ₁ G' H' hsp1 hsp2
  have hm3 := maximalIdeal_eq_span q hKK' red a x ϖ ϖ' G' H' hmK hmax' hmK' hπ₁ hQ hQ'
  have hGH' := congrArg (inclNode q hKK' red a) hGH₀
  rw [map_mul (inclNode q hKK' red a), map_mul (inclNode q hKK' red a), map_pow (inclNode q hKK' red a), inclNode_evHom_C, hϖ₁] at hGH'
  have huv : inclNode q hKK' red a G' * inclNode q hKK' red a H' =
      evHom q red a K' (MvPolynomial.C ϖ') ^ (e₁ * (d * eK)) *
        (evHom q red a K' (MvPolynomial.C (η : ↥(coeffSubring A K'))) ^ (d * eK) * inclNode q hKK' red a w) := by
    rw [hGH']
    ring
  have hwR : IsUnit (evHom q red a K' (MvPolynomial.C (η : ↥(coeffSubring A K'))) ^ (d * eK) * inclNode q hKK' red a w) :=
    (hηu.pow _).mul (hw.map (inclNode q hKK' red a))

  obtain ⟨J, hJ, hπJ, huJ, hJ1, hucJ, hJgen⟩ :=
    CrossingSectionPrime.exists_section_prime hc₀R hae han huv hm3 hQ hQ' huQ' hvQ hdim

  have hic : IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) := by
    letI : Algebra ↥(coeffSubring A K') ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) :=
      ((evHom q red a K').comp MvPolynomial.C).toAlgebra
    exact IsLocalRing.isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit ϖ' hirr
      (node_residue_surjective q red a K' hker (inclCoeff (A := A) hKK' x) hx' hdvr hirr) _ _ _ hwR _
      (lt_of_le_of_lt hae han).le huv hm3 hQ hQ' hvQ huQ'
  have hle : jIntegralClosure (1 * q) A K' ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q) :=
    jIntegralClosure_le_node q K' red hker a (inclCoeff (A := A) hKK' x) hx' hdvr hirr hic
  letI : Algebra ↥(jIntegralClosure (1 * q) A K') ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) :=
    (Subring.inclusion hle).toAlgebra
  haveI hloc : IsLocalization ((IsUnit.submonoid ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))).comap
      (Subring.inclusion hle)) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) :=
    isLocalization_node q K' red hker a (inclCoeff (A := A) hKK' x) hx' hdvr hirr hle

  have hJ1' : (Ideal.comap (Subring.inclusion hle) J).height = 1 := by
    letI : Algebra ↥(jIntegralClosure (1 * q) A K') ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q)) := (Subring.inclusion hle).toAlgebra
    exact (IsLocalization.height_under ((IsUnit.submonoid ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))).comap (Subring.inclusion hle)) J).trans hJ1
  have hGF : (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' :=
    node_le_fieldOver q K' red hker a (inclCoeff (A := A) hKK' x) hx' hdvr hirr (node_le_node q hKK' red a G'.2)
  have hunit : ∀ t : MvPolynomial (Fin 2) ↥(coeffSubring A K'),
      pointEval (coeffSubring A K') (redRestrict red K') a (a ^ q) t ≠ 0 → IsUnit (evHom q red a K' t) :=
    fun _ ht => isUnit_evHom_of_pointEval_ne_zero q red a K' hker (inclCoeff (A := A) hKK' x) hx' hdvr hirr ht
  have hval : evHom q red a K' (MvPolynomial.C (valueElt (A := A) c hcK')) =
      evHom q red a K' (MvPolynomial.C ϖ') ^ ae * evHom q red a K' (MvPolynomial.C (cu : ↥(coeffSubring A K'))) := by
    rw [hcu, MvPolynomial.C_mul, MvPolynomial.C_pow, map_mul (evHom q red a K'), map_pow (evHom q red a K')]
    exact mul_comm _ _
  rw [← hval] at hucJ hJgen
  have hg0 : inclNode q hKK' red a G' - evHom q red a K' (MvPolynomial.C (valueElt (A := A) c hcK')) ≠ 0 := by
    rw [hval]
    exact CrossingSectionPrime.sub_value_ne_zero (c₀ := evHom q red a K' (MvPolynomial.C (cu : ↥(coeffSubring A K')))) hae huQ'
  have hqO : ((q : ℕ) : ↥(coeffSubring A K')) = inclCoeff (A := A) hKK' ϖ ^ eK * inclCoeff (A := A) hKK' ε := by
    rw [← map_natCast (inclCoeff (A := A) hKK'), hqϖ, map_mul (inclCoeff (A := A) hKK'), map_pow (inclCoeff (A := A) hKK')]
  have hqR : ((q : ℕ) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))) =
      (evHom q red a K' (MvPolynomial.C (η : ↥(coeffSubring A K'))) * evHom q red a K' (MvPolynomial.C ϖ') ^ e₁) ^ eK *
        evHom q red a K' (MvPolynomial.C (inclCoeff (A := A) hKK' ε)) := by
    rw [← map_natCast ((evHom q red a K').comp MvPolynomial.C) q, RingHom.comp_apply, hqO, hη]
    simp only [map_mul, map_pow]
  have hqJ : ((q : ℕ) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K') (redRestrict red K') a (a ^ q))) ∉ J := by
    rw [hqR]
    exact CrossingSectionPrime.pow_mul_notMem hJ hπJ hηu hεu e₁ eK
  exact conjuncts q red a hKK' G' hGF c hcK' hunit hle J hJ hJ1' hqJ huJ hucJ hg0 hJgen

end NodeSectionPrime

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (ha : (0 : k) ∈ ssJSet q k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) ^ (jWidth (0 : k) * eK) * w)
    (hmax : ∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G', H'})
    (heK1 : 1 ≤ eK)
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))})
    (c : A) (hc : c ∈ IsLocalRing.maximalIdeal A)
    (hadm : ∃ m, m ∈ IsLocalRing.maximalIdeal A ∧ c * m = ((q : ℕ) : A) ^ 3)
    (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K'] (hKK' : K ≤ K')
    (hcK' : (c : AlgebraicClosure ℚ) ∈ K') :
    (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' ∧
    ∃ (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K')), 𝔭.IsPrime ∧ 𝔭.height = 1 ∧
      ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K')) ∉ 𝔭 ∧
      (∀ s : MvPolynomial (Fin 2) ↥(coeffSubring A K'),
        pointEval (coeffSubring A K') (redRestrict red K') (0 : k) ((0 : k) ^ q) s ≠ 0 →
          ∀ hs : modularEval (1 * q) (coeffSubring A K') s ∈ jIntegralClosure (1 * q) A K',
            (⟨_, hs⟩ : ↥(jIntegralClosure (1 * q) A K')) ∉ 𝔭) ∧
      ∃ r₀ r s : ↥(jIntegralClosure (1 * q) A K'), s ∉ 𝔭 ∧ r ∈ 𝔭 ∧
        (G' : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) = r₀ ∧
        ((G' : LaurentSeries (AlgebraicClosure ℚ))
            - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ))
          * (s : LaurentSeries (AlgebraicClosure ℚ)) = r ∧
        r ≠ 0 ∧ ∀ t ∈ 𝔭, ∃ u v : ↥(jIntegralClosure (1 * q) A K'), v ∉ 𝔭 ∧ t * v = r * u := by
  have _ := hq
  have _ := ha
  have _ := heK1
  have _ := hpr1
  have _ := hpr2
  have _ := hnm1
  have _ := hnm2
  have hGH3 : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) ^ (3 * eK) * w := by
    rw [hGH, jWidth_of_eq_zero rfl]
  exact NodeSectionPrime.main red hker (0 : k) (zero_pow (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero)) K ϖ hϖ eK ε hε hqϖ G' H' w hw 3
    hGH3 hmax hsp1 hsp2 0 (map_zero (redRestrict red K)) c hc hadm K' hKK' hcK'

end

end S_ModularCurve_NodeLocalized_exists_heightOnePrime_sectionOfCrossingParam_centred_zero
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_heightOnePrime_sectionOfCrossingParam_centred_zero (solution)
