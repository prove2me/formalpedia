-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6efb78a1-002b-512b-9eb5-d5fe2395dd0d

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem
import Theorems.Thm_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst
import Theorems.Thm_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow
import Theorems.Thm_ModularCurve_NodeLocalized_ord_modularRedLocHom_eq_iff_exists_isUnit
import Theorems.Thm_ModularCurve_exists_place_centred_node_of_height_one_of_natCast_notMem
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import Theorems.Thm_ModularCurve_exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

namespace L2G

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
private theorem mem_pair_left (a b : R) : a ∈ Ideal.span ({a, b} : Set R) :=
  Ideal.subset_span (Set.mem_insert _ _)

omit [IsDomain R] in
private theorem mem_pair_right (a b : R) : b ∈ Ideal.span ({a, b} : Set R) :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

omit [IsDomain R] in

private theorem dvd_mul_of_mem {ϖ X Y W : R} {e : ℕ} (he : 1 ≤ e) (hXY : X * Y = ϖ ^ e * W)
    {x : R} (hx : x ∈ Ideal.span ({ϖ, X} : Set R)) : ϖ ∣ x * Y := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  refine ⟨a * Y + b * ϖ ^ e' * W, ?_⟩
  calc (a * ϖ + b * X) * Y = a * ϖ * Y + b * (X * Y) := by ring
    _ = a * ϖ * Y + b * (ϖ ^ (e' + 1) * W) := by rw [hXY]
    _ = ϖ * (a * Y + b * ϖ ^ e' * W) := by ring

omit [IsDomain R] in

private theorem dvd_of_mem_mem {ϖ G H W : R} {e : ℕ} (he : 1 ≤ e) (hGH : G * H = ϖ ^ e * W)
    (hp2 : (Ideal.span ({ϖ, H} : Set R)).IsPrime) (hG2 : G ∉ Ideal.span ({ϖ, H} : Set R))
    {x : R} (h1 : x ∈ Ideal.span ({ϖ, G} : Set R)) (h2 : x ∈ Ideal.span ({ϖ, H} : Set R)) :
    ϖ ∣ x := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp h1
  have hbG : b * G ∈ Ideal.span ({ϖ, H} : Set R) := by
    have := Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ a (mem_pair_left ϖ H))
    rwa [add_sub_cancel_left] at this
  have hb : b ∈ Ideal.span ({ϖ, H} : Set R) := (hp2.mem_or_mem hbG).resolve_right hG2
  obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hb
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  refine ⟨a + c * G + d * ϖ ^ e' * W, ?_⟩
  calc a * ϖ + (c * ϖ + d * H) * G = a * ϖ + c * ϖ * G + d * (G * H) := by ring
    _ = a * ϖ + c * ϖ * G + d * (ϖ ^ (e' + 1) * W) := by rw [hGH]
    _ = ϖ * (a + c * G + d * ϖ ^ e' * W) := by ring

private theorem exists_mul_eq_pow_of_notMem {ϖ X Y W : R} {e : ℕ} (he : 1 ≤ e) (hXY : X * Y = ϖ ^ e * W)
    (hp : (Ideal.span ({ϖ, X} : Set R)).IsPrime)
    (hϖ0 : ϖ ≠ 0) :
    ∀ (n t : ℕ) (g c : R), g ∉ Ideal.span ({ϖ, X} : Set R) → g * c = ϖ ^ n * Y ^ t →
      ∃ (y : R) (t' : ℕ), g * y = Y ^ t' := by
  intro n
  induction n with
  | zero =>
    intro t g c _ hgc
    exact ⟨c, t, by rw [hgc, pow_zero, one_mul]⟩
  | succ n ih =>
    intro t g c hg hgc
    have hgc_mem : g * c ∈ Ideal.span ({ϖ, X} : Set R) := by
      rw [hgc]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (mem_pair_left ϖ X) _ n.succ_pos)
    have hc : c ∈ Ideal.span ({ϖ, X} : Set R) := (hp.mem_or_mem hgc_mem).resolve_left hg
    obtain ⟨c', hc'⟩ := dvd_mul_of_mem he hXY hc
    have key : g * c' = ϖ ^ n * Y ^ (t + 1) := by
      apply mul_left_cancel₀ hϖ0
      calc ϖ * (g * c') = g * (c * Y) := by rw [hc']; ring
        _ = (g * c) * Y := by ring
        _ = ϖ ^ (n + 1) * Y ^ t * Y := by rw [hgc]
        _ = ϖ * (ϖ ^ n * Y ^ (t + 1)) := by ring
    exact ih (t + 1) g c' hg key

private theorem exists_assoc_pow {ϖ X Y W : R} {e : ℕ} (he : 1 ≤ e) (hXY : X * Y = ϖ ^ e * W)
    (hp : (Ideal.span ({ϖ, X} : Set R)).IsPrime)
    (hϖ0 : ϖ ≠ 0) :
    ∀ (n t : ℕ) (g c : R), g * c = ϖ ^ n * Y ^ t →
      ∃ (α : ℕ) (z z' : R) (t₁ t₂ : ℕ), g * z = ϖ ^ α * Y ^ t₁ ∧ ϖ ^ α * z' = g * Y ^ t₂ := by
  intro n
  induction n with
  | zero =>
    intro t g c hgc
    exact ⟨0, c, g, t, 0, hgc, by ring⟩
  | succ n ih =>
    intro t g c hgc
    by_cases hg : g ∈ Ideal.span ({ϖ, X} : Set R)
    · obtain ⟨g', hg'⟩ := dvd_mul_of_mem he hXY hg
      have key : g' * c = ϖ ^ n * Y ^ (t + 1) := by
        apply mul_left_cancel₀ hϖ0
        calc ϖ * (g' * c) = (g * Y) * c := by rw [hg']; ring
          _ = (g * c) * Y := by ring
          _ = ϖ ^ (n + 1) * Y ^ t * Y := by rw [hgc]
          _ = ϖ * (ϖ ^ n * Y ^ (t + 1)) := by ring
      obtain ⟨α, z, z', t₁, t₂, h1, h2⟩ := ih (t + 1) g' c key
      refine ⟨α + 1, Y * z, z', t₁, t₂ + 1, ?_, ?_⟩
      · calc g * (Y * z) = (g * Y) * z := by ring
          _ = ϖ * (g' * z) := by rw [hg']; ring
          _ = ϖ * (ϖ ^ α * Y ^ t₁) := by rw [h1]
          _ = ϖ ^ (α + 1) * Y ^ t₁ := by ring
      · calc ϖ ^ (α + 1) * z' = ϖ * (ϖ ^ α * z') := by ring
          _ = ϖ * (g' * Y ^ t₂) := by rw [h2]
          _ = (g * Y) * Y ^ t₂ := by rw [hg']; ring
          _ = g * Y ^ (t₂ + 1) := by ring
    · obtain ⟨y, t', hy⟩ := exists_mul_eq_pow_of_notMem he hXY hp hϖ0 (n + 1) t g c hg hgc
      exact ⟨0, y, g, t', 0, by rw [hy]; ring, by ring⟩

private theorem dvd_of_hartogs {ϖ G H W : R} {e : ℕ} (hW : IsUnit W) (hGH : G * H = ϖ ^ e * W)
    (hp1 : (Ideal.span ({ϖ, G} : Set R)).IsPrime) (hH1 : H ∉ Ideal.span ({ϖ, G} : Set R))
    (hϖ0 : ϖ ≠ 0)
    (hHart : ∀ x : FractionRing R, (∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∃ r s : R, s ∉ p ∧ x * algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) r) →
      ∃ r : R, algebraMap R (FractionRing R) r = x)
    {a b : R} (hb : b ≠ 0) (hG : ∃ (s : ℕ) (c : R), a * G ^ s = b * c)
    (hH : ∃ (t : ℕ) (d : R), a * H ^ t = b * d) : b ∣ a := by
  have hinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hbK : algebraMap R (FractionRing R) b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
  obtain ⟨r, hr⟩ := hHart (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) (by
    intro p _ hp
    by_cases hGp : G ∈ p
    · by_cases hHp : H ∈ p
      · exfalso
        have hϖp : ϖ ∈ p := by
          have hmem : ϖ ^ e * W ∈ p := by
            rw [← hGH]
            exact Ideal.mul_mem_right _ _ hGp
          rcases ‹p.IsPrime›.mem_or_mem hmem with h | h
          · exact ‹p.IsPrime›.mem_of_pow_mem e h
          · exact absurd (Ideal.eq_top_of_isUnit_mem _ h hW) ‹p.IsPrime›.ne_top
        have hle : Ideal.span ({ϖ, G} : Set R) ≤ p := by
          rw [Ideal.span_le]
          rintro x (rfl | rfl)
          · exact hϖp
          · exact hGp
        have hlt : Ideal.span ({ϖ, G} : Set R) < p :=
          lt_of_le_of_ne hle (fun h => hH1 (by rw [h]; exact hHp))
        have hbot : (⊥ : Ideal R) < Ideal.span ({ϖ, G} : Set R) := by
          refine bot_lt_iff_ne_bot.mpr (fun h => hϖ0 ?_)
          have hmem := mem_pair_left ϖ G
          rw [h] at hmem
          exact Ideal.mem_bot.mp hmem
        have hp1' : p.height ≤ (1 : ℕ) := by rw [Nat.cast_one]; exact hp.le
        haveI := hp1
        have hlt1 := Ideal.height_le_iff.mp hp1' (Ideal.span ({ϖ, G} : Set R)) hp1 hlt
        rw [Nat.cast_one, ENat.lt_one_iff_eq_zero] at hlt1
        have hle0 : (Ideal.span ({ϖ, G} : Set R)).height ≤ (0 : ℕ) := by
          rw [Nat.cast_zero]; exact hlt1.le
        have hbot' := Ideal.height_le_iff.mp hle0 ⊥ Ideal.isPrime_bot hbot
        rw [Nat.cast_zero] at hbot'
        exact absurd hbot' not_lt_zero
      · obtain ⟨t, d, hd⟩ := hH
        refine ⟨d, H ^ t, fun h => hHp (‹p.IsPrime›.mem_of_pow_mem t h), ?_⟩
        rw [div_mul_eq_mul_div, ← map_mul, hd, map_mul, mul_div_cancel_left₀ _ hbK]
    · obtain ⟨s, c, hc⟩ := hG
      refine ⟨c, G ^ s, fun h => hGp (‹p.IsPrime›.mem_of_pow_mem s h), ?_⟩
      rw [div_mul_eq_mul_div, ← map_mul, hc, map_mul, mul_div_cancel_left₀ _ hbK])
  refine ⟨r, hinj ?_⟩
  rw [map_mul, hr, mul_comm, div_mul_cancel₀ _ hbK]

private theorem eq_pow_sub_of_pow_mul_eq_pow {X a : R} (hX0 : X ≠ 0) (hXu : ¬ IsUnit X) {m t : ℕ}
    (h : X ^ m * a = X ^ t) : m ≤ t ∧ a = X ^ (t - m) := by
  by_cases hmt : m ≤ t
  · refine ⟨hmt, mul_left_cancel₀ (pow_ne_zero m hX0) ?_⟩
    rw [h, ← pow_add, Nat.add_sub_cancel' hmt]
  · exfalso
    have hlt : t < m := Nat.lt_of_not_le hmt
    have h1 : X ^ t * (X ^ (m - t) * a) = X ^ t * 1 := by
      rw [mul_one, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le, h]
    have h2 := mul_left_cancel₀ (pow_ne_zero t hX0) h1
    obtain ⟨k, hk⟩ : ∃ k, m - t = k + 1 := ⟨m - t - 1, by omega⟩
    rw [hk, pow_succ] at h2
    exact hXu (IsUnit.of_mul_eq_one (X ^ k * a) (by rw [← h2]; ring))

private theorem exp_eq_of_pow_mul_unit_aux {D : Type*} [CommRing D] [IsDomain D] {x : D} (hx0 : x ≠ 0)
    (hxu : ¬ IsUnit x) {a b : ℕ} {u v : D} (hu : IsUnit u) (hab : a ≤ b)
    (h : x ^ a * u = x ^ b * v) : a = b := by
  have h1 : x ^ a * u = x ^ a * (x ^ (b - a) * v) := by
    rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab]
  have h2 := mul_left_cancel₀ (pow_ne_zero a hx0) h1
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, b - a = k + 1 := ⟨b - a - 1, by omega⟩
  refine hxu (isUnit_of_dvd_unit ⟨x ^ k * v, ?_⟩ hu)
  rw [h2, hk, pow_succ]; ring

private theorem exp_eq_of_pow_mul_unit {D : Type*} [CommRing D] [IsDomain D] {x : D} (hx0 : x ≠ 0)
    (hxu : ¬ IsUnit x) {a b : ℕ} {u v : D} (hu : IsUnit u) (hv : IsUnit v)
    (h : x ^ a * u = x ^ b * v) : a = b := by
  rcases le_total a b with hab | hba
  · exact exp_eq_of_pow_mul_unit_aux hx0 hxu hu hab h
  · exact (exp_eq_of_pow_mul_unit_aux hx0 hxu hv hba h.symm).symm

omit [IsDomain R] in
private theorem not_isUnit_mk_of_span_ne_top {ϖ G H : R} (hloc : Ideal.span ({ϖ, G, H} : Set R) ≠ ⊤) :
    ¬ IsUnit (Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) H) := by
  intro hunit
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  obtain ⟨v', rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, ← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.eq] at hv
  apply hloc
  rw [Ideal.eq_top_iff_one]
  have hsub : ({ϖ, G} : Set R) ⊆ ({ϖ, G, H} : Set R) :=
    Set.insert_subset_insert (Set.singleton_subset_iff.mpr (Set.mem_insert G {H}))
  have h1 : H * v' - 1 ∈ Ideal.span ({ϖ, G, H} : Set R) := Ideal.span_mono hsub hv
  have h2 : H * v' ∈ Ideal.span ({ϖ, G, H} : Set R) :=
    Ideal.mul_mem_right _ _ (Ideal.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton H))))
  have := Ideal.sub_mem _ h2 h1
  rwa [sub_sub_cancel] at this

private theorem case_notMem_fst {ϖ G H W : R} {e : ℕ} (he : 1 ≤ e) (hW : IsUnit W)
    (hGH : G * H = ϖ ^ e * W)
    (hp1 : (Ideal.span ({ϖ, G} : Set R)).IsPrime) (hp2 : (Ideal.span ({ϖ, H} : Set R)).IsPrime)
    (hH1 : H ∉ Ideal.span ({ϖ, G} : Set R)) (hG2 : G ∉ Ideal.span ({ϖ, H} : Set R))
    (hloc : Ideal.span ({ϖ, G, H} : Set R) ≠ ⊤)
    (BR1 : ∀ x : R, x ∉ Ideal.span ({ϖ, G} : Set R) →
      ∃ (s : ℕ) (u : R), IsUnit u ∧ x - H ^ s * u ∈ Ideal.span ({ϖ, G} : Set R))
    (hHart : ∀ x : FractionRing R, (∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∃ r s : R, s ∉ p ∧ x * algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) r) →
      ∃ r : R, algebraMap R (FractionRing R) r = x)
    (g : R) (hg0 : g ≠ 0) (n : ℕ) (hgn : g ∣ ϖ ^ n) (hg1 : g ∉ Ideal.span ({ϖ, G} : Set R)) :
    ∃ (j : ℕ) (u : R), IsUnit u ∧ g = H ^ j * u := by

  have hG0 : G ≠ 0 := fun h => hG2 (by rw [h]; exact Ideal.zero_mem _)
  have hH0 : H ≠ 0 := fun h => hH1 (by rw [h]; exact Ideal.zero_mem _)
  have hHu : ¬ IsUnit H := fun h =>
    hp2.ne_top (Ideal.eq_top_of_isUnit_mem _ (mem_pair_right ϖ H) h)
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : e ≠ 0), zero_mul] at hGH
    rcases mul_eq_zero.mp hGH with h' | h'
    · exact hG0 h'
    · exact hH0 h'
  obtain ⟨Wi, hWi⟩ := hW.exists_right_inv
  have hϖe : ϖ ^ e = G * H * Wi := by
    calc ϖ ^ e = ϖ ^ e * (W * Wi) := by rw [hWi, mul_one]
      _ = (ϖ ^ e * W) * Wi := by ring
      _ = G * H * Wi := by rw [← hGH]
  have hHG : H * G = ϖ ^ e * W := by rw [mul_comm]; exact hGH
  obtain ⟨c, hc⟩ := hgn
  have hgc : g * c = ϖ ^ n * G ^ 0 := by rw [pow_zero, mul_one]; exact hc.symm
  have hgc' : g * c = ϖ ^ n * H ^ 0 := by rw [pow_zero, mul_one]; exact hc.symm

  obtain ⟨β, z, z', t₁, t₂, hz, hz'⟩ := exists_assoc_pow he hHG hp2 hϖ0 n 0 g c hgc
  obtain ⟨y, t, hy⟩ := exists_mul_eq_pow_of_notMem he hGH hp1 hϖ0 n 0 g c hg1 hgc'

  obtain ⟨w, hw⟩ : H ^ β ∣ g ^ e :=
    dvd_of_hartogs hW hGH hp1 hH1 hϖ0 hHart (pow_ne_zero β hH0)
      ⟨t₂ * e, G ^ β * Wi ^ β * z' ^ e, by
        calc g ^ e * G ^ (t₂ * e) = (g * G ^ t₂) ^ e := by ring
          _ = (ϖ ^ β * z') ^ e := by rw [hz']
          _ = (ϖ ^ e) ^ β * z' ^ e := by ring
          _ = H ^ β * (G ^ β * Wi ^ β * z' ^ e) := by rw [hϖe]; ring⟩
      ⟨β, g ^ e, by ring⟩
  have hge0 : g ^ e ≠ 0 := pow_ne_zero e hg0
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hw
    exact hge0 hw

  have hwu : IsUnit w := by
    refine isUnit_of_dvd_one (dvd_of_hartogs hW hGH hp1 hH1 hϖ0 hHart hw0 ?_ ?_)
    · refine ⟨β + t₁ * e, z ^ e * W ^ β, ?_⟩
      have h1 : H ^ β * (w * z ^ e) = H ^ β * (G ^ (β + t₁ * e) * Wi ^ β) := by
        calc H ^ β * (w * z ^ e) = (H ^ β * w) * z ^ e := by ring
          _ = g ^ e * z ^ e := by rw [hw]
          _ = (g * z) ^ e := by ring
          _ = (ϖ ^ β * G ^ t₁) ^ e := by rw [hz]
          _ = (ϖ ^ e) ^ β * G ^ (t₁ * e) := by ring
          _ = H ^ β * (G ^ (β + t₁ * e) * Wi ^ β) := by rw [hϖe]; ring
      have h2 := mul_left_cancel₀ (pow_ne_zero β hH0) h1
      calc 1 * G ^ (β + t₁ * e) = G ^ (β + t₁ * e) * (W * Wi) ^ β := by
            rw [hWi, one_pow, mul_one, one_mul]
        _ = (w * z ^ e) * W ^ β := by rw [h2]; ring
        _ = w * (z ^ e * W ^ β) := by ring
    · have h3 : H ^ β * (w * y ^ e) = H ^ (t * e) := by
        calc H ^ β * (w * y ^ e) = (H ^ β * w) * y ^ e := by ring
          _ = g ^ e * y ^ e := by rw [hw]
          _ = (g * y) ^ e := by ring
          _ = H ^ (t * e) := by rw [hy]; ring
      obtain ⟨_, h4⟩ := eq_pow_sub_of_pow_mul_eq_pow hH0 hHu h3
      exact ⟨t * e - β, y ^ e, by rw [one_mul]; exact h4.symm⟩

  obtain ⟨s, u, hu, hsu⟩ := BR1 g hg1
  haveI := hp1
  have hπg : Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) g
      = Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) H ^ s
        * Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) u := by
    have : Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) (g - H ^ s * u) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hsu
    rwa [map_sub, sub_eq_zero, map_mul, map_pow] at this
  have hπH0 : Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) H ≠ 0 :=
    fun h => hH1 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hπHu := not_isUnit_mk_of_span_ne_top hloc
  have hrel : Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) H ^ (s * e)
        * (Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) u ^ e)
      = Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) H ^ β
        * Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) w := by
    calc Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) H ^ (s * e)
          * (Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) u ^ e)
        = (Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) H ^ s
            * Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) u) ^ e := by ring
      _ = (Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) g) ^ e := by rw [hπg]
      _ = Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) (g ^ e) := by rw [map_pow]
      _ = Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) (H ^ β * w) := by rw [hw]
      _ = Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) H ^ β
          * Ideal.Quotient.mk (Ideal.span ({ϖ, G} : Set R)) w := by rw [map_mul, map_pow]
  have hse : s * e = β :=
    exp_eq_of_pow_mul_unit hπH0 hπHu ((hu.map _).pow e) (hwu.map _) hrel
  subst hse

  obtain ⟨g', hg'⟩ : H ^ s ∣ g :=
    dvd_of_hartogs hW hGH hp1 hH1 hϖ0 hHart (pow_ne_zero s hH0)
      ⟨t₂, G ^ s * Wi ^ s * z', by
        calc g * G ^ t₂ = ϖ ^ (s * e) * z' := hz'.symm
          _ = (ϖ ^ e) ^ s * z' := by ring
          _ = H ^ s * (G ^ s * Wi ^ s * z') := by rw [hϖe]; ring⟩
      ⟨s, g, by ring⟩
  have hg'0 : g' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hg'
    exact hg0 hg'

  have F1 : H ^ s * (g' * y) = H ^ t := by
    calc H ^ s * (g' * y) = (H ^ s * g') * y := by ring
      _ = g * y := by rw [← hg']
      _ = H ^ t := hy
  obtain ⟨_, F1'⟩ := eq_pow_sub_of_pow_mul_eq_pow hH0 hHu F1
  have F2 : H ^ s * (g' * z) = H ^ s * (G ^ (s + t₁) * Wi ^ s) := by
    calc H ^ s * (g' * z) = (H ^ s * g') * z := by ring
      _ = g * z := by rw [← hg']
      _ = ϖ ^ (s * e) * G ^ t₁ := hz
      _ = (ϖ ^ e) ^ s * G ^ t₁ := by ring
      _ = H ^ s * (G ^ (s + t₁) * Wi ^ s) := by rw [hϖe]; ring
  have F2' := mul_left_cancel₀ (pow_ne_zero s hH0) F2
  have hg'u : IsUnit g' := by
    refine isUnit_of_dvd_one (dvd_of_hartogs hW hGH hp1 hH1 hϖ0 hHart hg'0 ?_ ?_)
    · refine ⟨s + t₁, z * W ^ s, ?_⟩
      calc 1 * G ^ (s + t₁) = G ^ (s + t₁) * (W * Wi) ^ s := by
            rw [hWi, one_pow, mul_one, one_mul]
        _ = (g' * z) * W ^ s := by rw [F2']; ring
        _ = g' * (z * W ^ s) := by ring
    · exact ⟨t - s, y, by rw [one_mul]; exact F1'.symm⟩
  exact ⟨s, g', hg'u, hg'⟩

private theorem case_notMem_snd {ϖ G H W : R} {e : ℕ} (he : 1 ≤ e) (hW : IsUnit W)
    (hGH : G * H = ϖ ^ e * W)
    (hp1 : (Ideal.span ({ϖ, G} : Set R)).IsPrime) (hp2 : (Ideal.span ({ϖ, H} : Set R)).IsPrime)
    (hH1 : H ∉ Ideal.span ({ϖ, G} : Set R)) (hG2 : G ∉ Ideal.span ({ϖ, H} : Set R))
    (hloc : Ideal.span ({ϖ, G, H} : Set R) ≠ ⊤)
    (BR1 : ∀ x : R, x ∉ Ideal.span ({ϖ, G} : Set R) →
      ∃ (s : ℕ) (u : R), IsUnit u ∧ x - H ^ s * u ∈ Ideal.span ({ϖ, G} : Set R))
    (hHart : ∀ x : FractionRing R, (∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∃ r s : R, s ∉ p ∧ x * algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) r) →
      ∃ r : R, algebraMap R (FractionRing R) r = x)
    (g : R) (hg0 : g ≠ 0) (n : ℕ) (hgn : g ∣ ϖ ^ n) (hg2 : g ∉ Ideal.span ({ϖ, H} : Set R)) :
    ∃ (i : ℕ) (u : R), IsUnit u ∧ g = G ^ i * u := by
  have hG0 : G ≠ 0 := fun h => hG2 (by rw [h]; exact Ideal.zero_mem _)
  have hH0 : H ≠ 0 := fun h => hH1 (by rw [h]; exact Ideal.zero_mem _)
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : e ≠ 0), zero_mul] at hGH
    rcases mul_eq_zero.mp hGH with h' | h'
    · exact hG0 h'
    · exact hH0 h'
  obtain ⟨Wi, hWi⟩ := hW.exists_right_inv
  have hWiu : IsUnit Wi := IsUnit.of_mul_eq_one W (by rw [mul_comm]; exact hWi)
  have hϖe : ϖ ^ e = G * H * Wi := by
    calc ϖ ^ e = ϖ ^ e * (W * Wi) := by rw [hWi, mul_one]
      _ = (ϖ ^ e * W) * Wi := by ring
      _ = G * H * Wi := by rw [← hGH]
  have hHG : H * G = ϖ ^ e * W := by rw [mul_comm]; exact hGH
  obtain ⟨c, hc⟩ := hgn
  have hgc : g * c = ϖ ^ n * H ^ 0 := by rw [pow_zero, mul_one]; exact hc.symm
  have hgc' : g * c = ϖ ^ n * G ^ 0 := by rw [pow_zero, mul_one]; exact hc.symm

  obtain ⟨α, z, z', t₁, t₂, hz, hz'⟩ := exists_assoc_pow he hGH hp1 hϖ0 n 0 g c hgc
  obtain ⟨y, t, hy⟩ := exists_mul_eq_pow_of_notMem he hHG hp2 hϖ0 n 0 g c hg2 hgc'

  obtain ⟨h, hh⟩ : g ∣ ϖ ^ α :=
    dvd_of_hartogs hW hGH hp1 hH1 hϖ0 hHart hg0
      ⟨t, y * ϖ ^ α, by
        calc ϖ ^ α * G ^ t = ϖ ^ α * (g * y) := by rw [hy]
          _ = g * (y * ϖ ^ α) := by ring⟩
      ⟨t₁, z, by rw [hz]⟩
  have hα0 : ϖ ^ α ≠ 0 := pow_ne_zero α hϖ0
  have hh0 : h ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hh
    exact hα0 hh
  have hhz : h * z' = H ^ t₂ := by
    apply mul_left_cancel₀ hg0
    calc g * (h * z') = (g * h) * z' := by ring
      _ = ϖ ^ α * z' := by rw [← hh]
      _ = g * H ^ t₂ := hz'
  have hh1 : h ∉ Ideal.span ({ϖ, G} : Set R) := by
    intro hmem
    have : H ^ t₂ ∈ Ideal.span ({ϖ, G} : Set R) := by
      rw [← hhz]; exact Ideal.mul_mem_right _ _ hmem
    exact hH1 (hp1.mem_of_pow_mem t₂ this)
  obtain ⟨j, u, hu, hju⟩ := case_notMem_fst he hW hGH hp1 hp2 hH1 hG2 hloc BR1 hHart h hh0 α
    ⟨g, by rw [hh, mul_comm]⟩ hh1

  obtain ⟨m, r, hr, hαmr⟩ : ∃ m r, r < e ∧ α = e * m + r :=
    ⟨α / e, α % e, Nat.mod_lt _ (by omega), (Nat.div_add_mod α e).symm⟩
  subst hαmr
  have hu2 : u ∉ Ideal.span ({ϖ, H} : Set R) := fun hmem =>
    hp2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  have hWi2 : ∀ k, Wi ^ k ∉ Ideal.span ({ϖ, H} : Set R) := fun k hmem =>
    hp2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hWiu.pow k))
  have hGk2 : ∀ k, G ^ k ∉ Ideal.span ({ϖ, H} : Set R) := fun k hmem =>
    hG2 (hp2.mem_of_pow_mem k hmem)
  have EQ : g * u * H ^ j = G ^ m * Wi ^ m * ϖ ^ r * H ^ m := by
    calc g * u * H ^ j = g * (H ^ j * u) := by ring
      _ = g * h := by rw [← hju]
      _ = ϖ ^ (e * m + r) := hh.symm
      _ = (ϖ ^ e) ^ m * ϖ ^ r := by ring
      _ = G ^ m * Wi ^ m * ϖ ^ r * H ^ m := by rw [hϖe]; ring
  have hgu2 : g * u ∉ Ideal.span ({ϖ, H} : Set R) := fun hmem =>
    (hp2.mem_or_mem hmem).elim hg2 hu2
  by_cases hjm : j ≤ m
  ·
    have EQ' : g * u = G ^ m * Wi ^ m * ϖ ^ r * H ^ (m - j) := by
      apply mul_left_cancel₀ (pow_ne_zero j hH0)
      calc H ^ j * (g * u) = g * u * H ^ j := by ring
        _ = G ^ m * Wi ^ m * ϖ ^ r * H ^ m := EQ
        _ = G ^ m * Wi ^ m * ϖ ^ r * (H ^ j * H ^ (m - j)) := by
            rw [← pow_add, Nat.add_sub_cancel' hjm]
        _ = H ^ j * (G ^ m * Wi ^ m * ϖ ^ r * H ^ (m - j)) := by ring
    have hmj : m - j = 0 := by
      by_contra hne
      apply hgu2
      rw [EQ']
      exact Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (mem_pair_right ϖ H) _ (Nat.pos_of_ne_zero hne))
    have hr0 : r = 0 := by
      by_contra hne
      apply hgu2
      rw [EQ']
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (mem_pair_left ϖ H) _ (Nat.pos_of_ne_zero hne)))
    rw [hmj, hr0, pow_zero, pow_zero, mul_one, mul_one] at EQ'
    obtain ⟨ui, hui⟩ := hu.exists_right_inv
    refine ⟨m, Wi ^ m * ui, (hWiu.pow m).mul (IsUnit.of_mul_eq_one u (by rw [mul_comm]; exact hui)), ?_⟩
    calc g = g * (u * ui) := by rw [hui, mul_one]
      _ = (g * u) * ui := by ring
      _ = G ^ m * Wi ^ m * ui := by rw [EQ']
      _ = G ^ m * (Wi ^ m * ui) := by ring
  · exfalso
    have hlt : m < j := Nat.lt_of_not_le hjm
    obtain ⟨k, hk⟩ : ∃ k, j = m + (k + 1) := ⟨j - m - 1, by omega⟩

    have EQ'' : g * u * H ^ (k + 1) = G ^ m * Wi ^ m * ϖ ^ r := by
      apply mul_left_cancel₀ (pow_ne_zero m hH0)
      calc H ^ m * (g * u * H ^ (k + 1)) = g * u * H ^ (m + (k + 1)) := by ring
        _ = g * u * H ^ j := by rw [hk]
        _ = G ^ m * Wi ^ m * ϖ ^ r * H ^ m := EQ
        _ = H ^ m * (G ^ m * Wi ^ m * ϖ ^ r) := by ring

    have EQ3 : ϖ ^ r * (ϖ ^ (e - r) * (W * (g * u * H ^ k))) = ϖ ^ r * (G ^ (m + 1) * Wi ^ m) := by
      calc ϖ ^ r * (ϖ ^ (e - r) * (W * (g * u * H ^ k)))
          = ϖ ^ (r + (e - r)) * W * (g * u * H ^ k) := by ring
        _ = ϖ ^ e * W * (g * u * H ^ k) := by rw [Nat.add_sub_cancel' hr.le]
        _ = G * H * (g * u * H ^ k) := by rw [← hGH]
        _ = G * (g * u * H ^ (k + 1)) := by ring
        _ = G * (G ^ m * Wi ^ m * ϖ ^ r) := by rw [EQ'']
        _ = ϖ ^ r * (G ^ (m + 1) * Wi ^ m) := by ring
    have EQ4 := mul_left_cancel₀ (pow_ne_zero r hϖ0) EQ3
    have hmem : G ^ (m + 1) * Wi ^ m ∈ Ideal.span ({ϖ, H} : Set R) := by
      rw [← EQ4]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_of_mem _ (mem_pair_left ϖ H) _ (by omega))
    exact (hp2.mem_or_mem hmem).elim (hGk2 (m + 1)) (hWi2 m)

private theorem monomial_of_dvd_pow {ϖ G H W : R} {e : ℕ} (he : 1 ≤ e) (hW : IsUnit W)
    (hGH : G * H = ϖ ^ e * W)
    (hp1 : (Ideal.span ({ϖ, G} : Set R)).IsPrime) (hp2 : (Ideal.span ({ϖ, H} : Set R)).IsPrime)
    (hH1 : H ∉ Ideal.span ({ϖ, G} : Set R)) (hG2 : G ∉ Ideal.span ({ϖ, H} : Set R))
    (hloc : Ideal.span ({ϖ, G, H} : Set R) ≠ ⊤)
    (BR1 : ∀ x : R, x ∉ Ideal.span ({ϖ, G} : Set R) →
      ∃ (s : ℕ) (u : R), IsUnit u ∧ x - H ^ s * u ∈ Ideal.span ({ϖ, G} : Set R))
    (hHart : ∀ x : FractionRing R, (∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∃ r s : R, s ∉ p ∧ x * algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) r) →
      ∃ r : R, algebraMap R (FractionRing R) r = x)
    (n : ℕ) : ∀ (g : R), g ≠ 0 → g ∣ ϖ ^ n →
      ∃ (l i j : ℕ) (u : R), IsUnit u ∧ g = ϖ ^ l * G ^ i * H ^ j * u := by
  have hG0 : G ≠ 0 := fun h => hG2 (by rw [h]; exact Ideal.zero_mem _)
  have hH0 : H ≠ 0 := fun h => hH1 (by rw [h]; exact Ideal.zero_mem _)
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    have hGH' := hGH
    rw [h, zero_pow (by omega : e ≠ 0), zero_mul] at hGH'
    rcases mul_eq_zero.mp hGH' with h' | h'
    · exact hG0 h'
    · exact hH0 h'
  induction n with
  | zero =>
    intro g _ hgn
    rw [pow_zero] at hgn
    exact ⟨0, 0, 0, g, isUnit_of_dvd_one hgn, by ring⟩
  | succ n ih =>
    intro g hg0 hgn
    by_cases h1 : g ∈ Ideal.span ({ϖ, G} : Set R)
    · by_cases h2 : g ∈ Ideal.span ({ϖ, H} : Set R)
      · obtain ⟨g₁, rfl⟩ := dvd_of_mem_mem he hGH hp2 hG2 h1 h2
        have hg₁0 : g₁ ≠ 0 := right_ne_zero_of_mul hg0
        have hg₁n : g₁ ∣ ϖ ^ n := by
          obtain ⟨c, hc⟩ := hgn
          refine ⟨c, mul_left_cancel₀ hϖ0 ?_⟩
          rw [← pow_succ', hc, mul_assoc]
        obtain ⟨l, i, j, u, hu, hEq⟩ := ih g₁ hg₁0 hg₁n
        exact ⟨l + 1, i, j, u, hu, by rw [hEq]; ring⟩
      · obtain ⟨i, u, hu, hEq⟩ :=
          case_notMem_snd he hW hGH hp1 hp2 hH1 hG2 hloc BR1 hHart g hg0 (n + 1) hgn h2
        exact ⟨0, i, 0, u, hu, by rw [hEq]; ring⟩
    · obtain ⟨j, u, hu, hEq⟩ :=
        case_notMem_fst he hW hGH hp1 hp2 hH1 hG2 hloc BR1 hHart g hg0 (n + 1) hgn h1
      exact ⟨0, 0, j, u, hu, by rw [hEq]; ring⟩

private theorem exists_dvd_pow_of_forall_height_one [IsNoetherianRing R] {ϖ g : R} (hg0 : g ≠ 0)
    (HOR : ∀ (P : Ideal R) [P.IsPrime], P.height = 1 → ϖ ∉ P → g ∉ P) :
    ∃ n : ℕ, g ∣ ϖ ^ n := by
  have hrad : ϖ ∈ (Ideal.span ({g} : Set R)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hgP, hP⟩
    haveI := hP
    obtain ⟨P', hP'min, hP'le⟩ := Ideal.exists_minimalPrimes_le hgP
    haveI := hP'min.1.1
    haveI : (Ideal.span ({g} : Set R)).IsPrincipal := ⟨⟨g, rfl⟩⟩
    have hle1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span ({g} : Set R)) P' hP'min
    have hgP' : g ∈ P' := hP'min.1.2 (Ideal.mem_span_singleton_self g)
    have hne : P' ≠ ⊥ := by
      intro h
      rw [h] at hgP'
      exact hg0 (Ideal.mem_bot.mp hgP')
    have hbot : (⊥ : Ideal R) < P' := bot_lt_iff_ne_bot.mpr hne
    have h1 : (1 : ℕ∞) ≤ P'.height := by
      by_contra hlt
      have h0 : P'.height ≤ (0 : ℕ) := by
        rw [Nat.cast_zero]
        exact (ENat.lt_one_iff_eq_zero.mp (not_le.mp hlt)).le
      have := Ideal.height_le_iff.mp h0 ⊥ Ideal.isPrime_bot hbot
      rw [Nat.cast_zero] at this
      exact absurd this not_lt_zero
    have hP'1 : P'.height = 1 := le_antisymm hle1 h1
    by_contra hϖP
    exact HOR P' hP'1 (fun h => hϖP (hP'le h)) hgP'
  obtain ⟨n, hn⟩ := hrad
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

end L2G

namespace L2H

private theorem modularEval_mem_jIntegralClosure {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ jIntegralClosure (1 * q) A K := by
  obtain ⟨hj, hjq⟩ := ModularCurve.NodeLocalized.jqModC_mem_jIntegralClosure_and_jqNModC_mem (q := q) A K
  have hjR : jRing A K ≤ jIntegralClosure (1 * q) A K := by
    intro x hx
    refine ⟨?_, ?_⟩
    · refine (Subring.closure_le.mpr ?_) hx
      rintro y (⟨c, rfl⟩ | rfl)
      · exact Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), c.2.2⟩, rfl⟩)
      · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
    · exact isIntegral_algebraMap (R := ↥(jRing A K)) (A := LaurentSeries (AlgebraicClosure ℚ)) (x := ⟨x, hx⟩)
  show MvPolynomial.eval₂ (CharPReduction.constSeries (coeffSubring A K))
    ![jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)] p ∈ jIntegralClosure (1 * q) A K
  refine MvPolynomial.eval₂_mem (fun i _ => ?_) (fun i => ?_)
  · exact hjR (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
  · fin_cases i
    · exact hj
    · exact hjq

private theorem coe_mem_fieldOver {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (y : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K := by
  obtain ⟨r, s, hs, hy⟩ := y.2
  have hsC := (modularEval_mem_jIntegralClosure (q := q) A K s).1
  have hrC := (modularEval_mem_jIntegralClosure (q := q) A K r).1
  have hs0 : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := fun h =>
    hs (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s h)
  have : (y : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) r * (modularEval (1 * q) (coeffSubring A K) s)⁻¹ := by
    rw [← hy, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [this]
  exact (fieldOver (1 * q) K).mul_mem hrC ((fieldOver (1 * q) K).inv_mem hsC)

private noncomputable def inclK (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(coeffSubring A K) →+* ↥A.toSubring :=
  Subring.inclusion inf_le_left

private theorem modularEval_map_inclK
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) A.toSubring (MvPolynomial.map (inclK A K) p) = modularEval (1 * q) (coeffSubring A K) p := by
  have hcomp : (CharPReduction.constSeries A.toSubring).comp (inclK A K) = CharPReduction.constSeries (coeffSubring A K) :=
    RingHom.ext fun _ => rfl
  simp only [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, hcomp]

private theorem pointEval_map_inclK
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k) (b c : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    pointEval A.toSubring red b c (MvPolynomial.map (inclK A K) s) = pointEval (coeffSubring A K) (redRestrict red K) b c s :=
  MvPolynomial.eval₂_map (inclK A K) ![b, c] red s

private theorem mem_nodeRingA_of_mem {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (y : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) := by
  obtain ⟨r, s, hs, hgs⟩ := y.2
  refine ⟨MvPolynomial.map (inclK A K) r, MvPolynomial.map (inclK A K) s, ?_, ?_⟩
  · rw [pointEval_map_inclK]; exact hs
  · rw [modularEval_map_inclK, modularEval_map_inclK]; exact hgs

private theorem jqModC_mem_modularFunctionFieldBar {q : ℕ} [Fact q.Prime] :
    jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar (1 * q) := by
  rw [← ModularCurve.coeffEmb_jq]
  exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))

private theorem jqNModC_mem_modularFunctionFieldBar {q : ℕ} [Fact q.Prime] :
    jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ modularFunctionFieldBar (1 * q) := by
  have h : jqNModC (AlgebraicClosure ℚ) (1 * q) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) := by
    rw [ModularCurve.coeffEmb_qExpand, ModularCurve.coeffEmb_jq, jqNModC]
  rw [h]
  exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))

private theorem modularEval_mem_modularFunctionFieldBar
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ modularFunctionFieldBar (1 * q) := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    rw [show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C x) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) from
        MvPolynomial.eval₂Hom_C _ _ x]
    exact IntermediateField.algebraMap_mem _ _
  | add p₁ p₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | mul_X p i h =>
    rw [map_mul]
    refine mul_mem h ?_
    rw [show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X i) =
        ![jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)] i from MvPolynomial.eval₂Hom_X' _ _ i]
    fin_cases i
    · exact jqModC_mem_modularFunctionFieldBar
    · exact jqNModC_mem_modularFunctionFieldBar

private theorem coe_mem_bar {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (y : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := by
  obtain ⟨r, s, hs, hgs⟩ := y.2
  have hs0 : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := fun h =>
    hs (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s h)
  have hgd : (y : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) r / modularEval (1 * q) (coeffSubring A K) s := by
    rw [eq_div_iff hs0]; exact hgs
  rw [hgd]
  exact div_mem (modularEval_mem_modularFunctionFieldBar A K r) (modularEval_mem_modularFunctionFieldBar A K s)

private theorem not_isUnit_modularEvalAt_of_pointEval_eq_zero {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K))
      ≤ RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)))]
    {p : MvPolynomial (Fin 2) ↥(coeffSubring A K)}
    (hp : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p = 0) :
    ¬ IsUnit (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p) := by
  rintro ⟨y, hy⟩
  obtain ⟨r', s', hs', hys⟩ := ((y⁻¹ : (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))ˣ) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))).2
  have h1 : modularEval (1 * q) (coeffSubring A K) p * (((y⁻¹ : (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))ˣ) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = 1 := by
    have h := congrArg (fun w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) => (w : LaurentSeries (AlgebraicClosure ℚ))) y.mul_inv
    rw [hy] at h
    exact h
  have h2 : modularEval (1 * q) (coeffSubring A K) (p * r' - s') = 0 := by
    rw [map_sub, map_mul, ← hys, ← mul_assoc, h1, one_mul (modularEval (1 * q) (coeffSubring A K) s'), sub_self]
  have h3 : p * r' - s' ∈ RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    (Fact.out : RingHom.ker (modularEval (1 * q) (coeffSubring A K))
      ≤ RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) ((RingHom.mem_ker).mpr h2)
  rw [RingHom.mem_ker, map_sub, map_mul, hp, zero_mul, zero_sub, neg_eq_zero] at h3
  exact hs' h3

private theorem jRing_le {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jRing A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  refine Subring.closure_le.mpr ?_
  rintro y (⟨c, rfl⟩ | rfl)
  · have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) = CharPReduction.constSeries (coeffSubring A K) c :=
      MvPolynomial.eval₂Hom_C _ _ c
    rw [← h]
    exact modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _
  · have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) =
        ![jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)] (0 : Fin 2) :=
      MvPolynomial.eval₂Hom_X' _ _ (0 : Fin 2)
    rw [show jqModC (AlgebraicClosure ℚ) = ![jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)] (0 : Fin 2)
      from rfl, ← h]
    exact modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _

private theorem jIntegralClosure_le {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hIC : IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    jIntegralClosure (1 * q) A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  intro c hc
  obtain ⟨hcF, hcI⟩ := hc

  obtain ⟨p, hpm, hpc⟩ := hcI
  haveI := hIC
  have hJR := jRing_le red a K (q := q)
  have hce : (algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (LaurentSeries (AlgebraicClosure ℚ))).comp (Subring.inclusion hJR) = algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) :=
    RingHom.ext fun _ => rfl

  obtain ⟨y, z, hy, hz, hz0, hcz⟩ := ModularCurve.NodeLocalized.exists_mul_eq_of_mem_fieldOver red a K hcF
  have hinj : Function.Injective (algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (LaurentSeries (AlgebraicClosure ℚ))) := Subtype.val_injective
  let φ : FractionRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+* LaurentSeries (AlgebraicClosure ℚ) := IsFractionRing.lift hinj
  have hφ : ∀ r : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)), φ (algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (FractionRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) r) = (r : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun r => IsFractionRing.lift_algebraMap hinj r
  set w : FractionRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (FractionRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ⟨y, hy⟩ / algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (FractionRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ⟨z, hz⟩ with hw
  have hφw : φ w = c := by
    rw [hw, map_div₀, hφ, hφ]
    show y / z = c
    rw [div_eq_iff hz0]
    exact hcz.symm
  have hwint : IsIntegral ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) w := by
    refine ⟨p.map (Subring.inclusion hJR), hpm.map _, ?_⟩
    apply φ.injective
    rw [Polynomial.hom_eval₂, hφw, map_zero]
    have hcomp : φ.comp (algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (FractionRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) = algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (LaurentSeries (AlgebraicClosure ℚ)) := RingHom.ext hφ
    rw [hcomp, Polynomial.eval₂_map, hce]
    exact hpc
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) (K := FractionRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))).mp hwint
  have : c = (r : LaurentSeries (AlgebraicClosure ℚ)) := by rw [← hφ r, hr, hφw]
  rw [this]
  exact r.2

private def nodeDenomC {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Submonoid ↥(jIntegralClosure (1 * q) A K) where
  carrier := {y | ∃ s : MvPolynomial (Fin 2) ↥(coeffSubring A K),
    pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0 ∧
      modularEval (1 * q) (coeffSubring A K) s = (y : LaurentSeries (AlgebraicClosure ℚ))}
  one_mem' := ⟨1, by rw [map_one]; exact one_ne_zero, by rw [map_one]; rfl⟩
  mul_mem' := by
    rintro y z ⟨s, hs, hys⟩ ⟨t, ht, hzt⟩
    exact ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, by rw [map_mul, hys, hzt]; rfl⟩

private theorem isLocalization_C {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K))
      ≤ RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)))]
    (hCle : jIntegralClosure (1 * q) A K
      ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :
    @IsLocalization _ _ (nodeDenomC red a K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) _ (Subring.inclusion hCle).toAlgebra := by
  letI := (Subring.inclusion hCle).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨y, s, hs, hys⟩
    have heq : algebraMap ↥(jIntegralClosure (1 * q) A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) y
        = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) s :=
      Subtype.ext hys.symm
    rw [heq]
    exact isUnit_modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) hs
  · intro z
    obtain ⟨r, s, hs, hz⟩ := z.2
    refine ⟨⟨⟨modularEval (1 * q) (coeffSubring A K) r, modularEval_mem_jIntegralClosure A K r⟩,
      ⟨⟨modularEval (1 * q) (coeffSubring A K) s, modularEval_mem_jIntegralClosure A K s⟩, s, hs, rfl⟩⟩, ?_⟩
    exact Subtype.ext hz
  · intro y z h
    refine ⟨1, ?_⟩
    rw [OneMemClass.coe_one, one_mul y, one_mul z]
    exact Subtype.ext (congrArg (fun w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) => (w : LaurentSeries (AlgebraicClosure ℚ))) h)

end L2H

namespace L2S

private theorem isIntegrallyClosed_nodeRing {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    [IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))] [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    [Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K))
      ≤ RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)))]
    (e : ℕ) (he : 1 ≤ e) (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ e * w)
    (hmax' : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'})
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime) (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}) (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}) :
    IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
  let κ : ↥(coeffSubring A K) →+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).comp MvPolynomial.C

  have hredq : redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero k q
  have hqnu : ¬ IsUnit ((q : ℕ) : ↥(coeffSubring A K)) := by
    intro hu
    have h := hu.map (redRestrict red K)
    rw [hredq] at h
    exact not_isUnit_zero h
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  haveI hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := by
    rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with hK | h
    · exfalso
      apply hqnu
      have hmem : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
        rw [hK]; exact K.inv_mem (IntermediateField.natCast_mem K q)
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
      simp [mul_inv_cancel₀ hq0]
    · exact h
  have hq0O : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
    intro h
    have h' : ((q : ℕ) : AlgebraicClosure ℚ) = 0 := by
      exact_mod_cast congrArg (fun c : ↥(coeffSubring A K) => (c : AlgebraicClosure ℚ)) h
    exact hq0 h'
  have hkerP : (RingHom.ker (redRestrict red K)).IsPrime := RingHom.ker_isPrime _
  have hkerne : RingHom.ker (redRestrict red K) ≠ ⊥ := by
    intro h
    have hmem : ((q : ℕ) : ↥(coeffSubring A K)) ∈ RingHom.ker (redRestrict red K) := (RingHom.mem_ker).mpr hredq
    rw [h, Ideal.mem_bot] at hmem
    exact hq0O hmem
  have hkermax : RingHom.ker (redRestrict red K) = IsLocalRing.maximalIdeal ↥(coeffSubring A K) := by
    haveI := hkerP
    exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hkerne)
  have hunif : IsLocalRing.maximalIdeal ↥(coeffSubring A K) = Ideal.span {ϖ} := by
    apply le_antisymm
    · intro c hc
      rw [← hkermax, RingHom.mem_ker] at hc
      obtain ⟨d, hd⟩ := (hϖ c).mp hc
      exact Ideal.mem_span_singleton'.mpr ⟨d, by rw [hd, mul_comm]⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ← hkermax, RingHom.mem_ker]
      exact (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hunif

  letI algO : Algebra ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := κ.toAlgebra
  have hκ : ∀ c : ↥(coeffSubring A K), algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) c = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C c) := fun c => rfl

  have hpe : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p = redRestrict red K (MvPolynomial.eval ![x, x ^ q] p) := by
    intro p
    have hfun : (![a, a ^ q] : Fin 2 → k) = (redRestrict red K) ∘ ![x, x ^ q] := by
      funext i; fin_cases i <;> simp [hx, map_pow]
    rw [pointEval, MvPolynomial.coe_eval₂Hom, hfun, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  have hCval : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p - algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (MvPolynomial.eval ![x, x ^ q] p) ∈ IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
    intro p
    rw [hκ, ← map_sub]
    refine (IsLocalRing.mem_maximalIdeal _).mpr (L2H.not_isUnit_modularEvalAt_of_pointEval_eq_zero red a K ?_)
    rw [map_sub, hpe p, show pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] p))
      = redRestrict red K (MvPolynomial.eval ![x, x ^ q] p) from MvPolynomial.eval₂Hom_C _ _ _, sub_self]

  have hres : Function.Surjective ((IsLocalRing.residue ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))).comp (algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) := by
    intro zbar
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zbar
    obtain ⟨r, s, hs, hz⟩ := z.2
    have hcs : IsUnit (MvPolynomial.eval ![x, x ^ q] s) := by
      by_contra hn
      have hmem : MvPolynomial.eval ![x, x ^ q] s ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) :=
        (IsLocalRing.mem_maximalIdeal _).mpr hn
      rw [← hkermax, RingHom.mem_ker, ← hpe] at hmem
      exact hs hmem
    obtain ⟨cu, hcu⟩ := hcs
    refine ⟨MvPolynomial.eval ![x, x ^ q] r * ↑cu⁻¹, ?_⟩
    rw [RingHom.comp_apply]
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    have hzs : (z : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) * modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) s = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r := Subtype.ext hz
    have hS : IsUnit (algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (↑cu : ↥(coeffSubring A K))) := cu.isUnit.map _
    have key : (algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (MvPolynomial.eval ![x, x ^ q] r * ↑cu⁻¹) - z) * algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ↑cu
        ∈ IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
      have e : (algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (MvPolynomial.eval ![x, x ^ q] r * ↑cu⁻¹) - z) * algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ↑cu
          = -(modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r - algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (MvPolynomial.eval ![x, x ^ q] r))
            + z * (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) s - algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (MvPolynomial.eval ![x, x ^ q] s)) := by
        rw [sub_mul, ← map_mul, Units.inv_mul_cancel_right, hcu, ← hzs]; ring
      rw [e]
      exact add_mem (neg_mem (hCval r)) (Ideal.mul_mem_left _ _ (hCval s))
    have e2 : algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (MvPolynomial.eval ![x, x ^ q] r * ↑cu⁻¹) - z
        = ((algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) (MvPolynomial.eval ![x, x ^ q] r * ↑cu⁻¹) - z) * algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ↑cu) * ↑(hS.unit⁻¹) := by
      rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [e2]
    exact Ideal.mul_mem_right _ _ key
  have hκϖ : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) = algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ := rfl
  have hGH2 : G' * H' = algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ ^ e * w := by rw [← hκϖ]; exact hGH
  have hmax2 : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, G', H'} := by
    rw [← hκϖ]; exact hmax'
  have hpr1' : (Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, G'}).IsPrime := by rw [← hκϖ]; exact hpr1
  have hpr2' : (Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, H'}).IsPrime := by rw [← hκϖ]; exact hpr2
  have hnm1' : H' ∉ Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, G'} := by rw [← hκϖ]; exact hnm1
  have hnm2' : G' ∉ Ideal.span {algebraMap ↥(coeffSubring A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ϖ, H'} := by rw [← hκϖ]; exact hnm2
  exact IsLocalRing.isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit ϖ hirr hres
    G' H' w hw e he hGH2 hmax2 hpr1' hpr2' hnm1' hnm2'

private theorem branchReading {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    (G' H' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) :
    ∀ y : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)), y ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} →
      ∃ (s : ℕ) (u : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), IsUnit u ∧ y - H' ^ s * u ∈ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} := by
  set ϖt : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) with hϖt
  set Gt : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) with hGt
  set Ht : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) with hHt
  have hHt1 : Ht ∉ Ideal.span ({ϖt, G'} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by
    intro hmem
    apply hnm1
    obtain ⟨γ, δ, hγδ⟩ := Ideal.mem_span_pair.mp (show H' ∈ Ideal.span ({ϖt, Ht} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) by
      rw [← hsp2]; exact L2G.mem_pair_right _ _)
    rw [← hγδ]
    exact add_mem (Ideal.mul_mem_left _ _ (L2G.mem_pair_left _ _)) (Ideal.mul_mem_left _ _ hmem)
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp (show Ht ∈ Ideal.span ({ϖt, H'} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) by
    rw [hsp2]; exact L2G.mem_pair_right _ _)
  have hβ : IsUnit β := by
    obtain ⟨γ, δ, hγδ⟩ := Ideal.mem_span_pair.mp (show H' ∈ Ideal.span ({ϖt, Ht} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) by
      rw [← hsp2]; exact L2G.mem_pair_right _ _)

    have hmem : (1 - β * δ) * Ht ∈ Ideal.span ({ϖt, G'} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by
      have : (1 - β * δ) * Ht = (α + β * γ) * ϖt - β * (γ * ϖt + δ * Ht - H') - (β * H' + α * ϖt - Ht) := by ring
      have h1 : β * H' + α * ϖt - Ht = 0 := by rw [← hαβ]; ring
      have h2 : γ * ϖt + δ * Ht - H' = 0 := by rw [← hγδ]; ring
      rw [this, h1, h2, mul_zero, sub_zero, sub_zero]
      exact Ideal.mul_mem_left _ _ (L2G.mem_pair_left _ _)
    have h1βδ : 1 - β * δ ∈ Ideal.span ({ϖt, G'} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
      (hpr1.mem_or_mem hmem).resolve_right hHt1
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (β * δ) with hu | hu
    · exact isUnit_of_mul_isUnit_left hu
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h1βδ hu) hpr1.ne_top
  intro y hy
  have hy' : y ∉ Ideal.span ({ϖt, Gt} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by rwa [← hsp1]
  have hyA := L2H.mem_nodeRingA_of_mem red a K y
  have hyF := L2H.coe_mem_bar red a K y
  obtain ⟨h₁, h₁F, -, -, -, -, -⟩ :=
    ModularCurve.exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint red a ha2 ⟨(y : LaurentSeries (AlgebraicClosure ℚ)), hyF⟩ hyA
  have hy0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 := fun h0' =>
    hy' ((ModularCurve.NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst
      red a ha2 K ϖ hϖ y h₁).mp h0')
  have hord0 : (0 : ℤ) ≤ (frobNodePair q a).1.ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) := by
    have h := (ModularCurve.NodeLocalized.natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow
      red a ha2 K ϖ hϖ y h₁ h₁F hy0 0).mpr (by
        rw [pow_zero, Ideal.span_singleton_one]
        exact Ideal.mem_sup_right Submodule.mem_top)
    exact_mod_cast h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (frobNodePair q a).1.ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = n :=
    ⟨_, (Int.toNat_of_nonneg hord0).symm⟩
  obtain ⟨u, hu, hmem⟩ := (ModularCurve.NodeLocalized.ord_modularRedLocHom_eq_iff_exists_isUnit
    red a ha2 K ϖ hϖ y h₁ h₁F hy0 n).mp hn

  refine ⟨n, β ^ n * u, (hβ.pow n).mul hu, ?_⟩
  rw [hsp1]
  have hdvd : Ht - β * H' ∣ Ht ^ n - (β * H') ^ n := sub_dvd_pow_sub_pow Ht (β * H') n
  obtain ⟨c, hc⟩ := hdvd
  have hdiff : Ht - β * H' = α * ϖt := by rw [← hαβ]; ring
  have hmemϖ : Ht ^ n * u - H' ^ n * (β ^ n * u) ∈ Ideal.span ({ϖt, Gt} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by
    have : Ht ^ n * u - H' ^ n * (β ^ n * u) = (Ht ^ n - (β * H') ^ n) * u := by ring
    rw [this, hc, hdiff]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (L2G.mem_pair_left _ _)))
  have : y - H' ^ n * (β ^ n * u) = (y - Ht ^ n * u) + (Ht ^ n * u - H' ^ n * (β ^ n * u)) := by ring
  rw [this]
  exact add_mem hmem hmemϖ

private theorem notMem_of_height_one {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    [Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K))
      ≤ RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q)))]
    (hIC : IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) (hg0 : g ≠ 0)
    (hgF : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q))
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord (⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : modularFunctionFieldBar (1 * q)) = 0) :
    ∀ (P : Ideal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) [P.IsPrime], P.height = 1 → (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∉ P → g ∉ P := by
  haveI := hIC
  set ϖt : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) with hϖt
  let κ : ↥(coeffSubring A K) →+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).comp MvPolynomial.C
  have hqR : ((q : ℕ) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) = ϖt ^ eK * κ ε := by
    have h : κ ((q : ℕ) : ↥(coeffSubring A K)) = κ (ϖ ^ eK * ε) := by rw [hqϖ]
    rw [map_natCast, map_mul, map_pow] at h
    exact h
  have hκε : IsUnit (κ ε) := hε.map κ

  set gB : ↥(modularFunctionFieldBar (1 * q)) := ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ with hgB
  have hg0L : (g : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => hg0 (Subtype.ext h)
  have hgB0 : gB ≠ 0 := fun h => hg0L (congrArg (fun w : ↥(modularFunctionFieldBar (1 * q)) => (w : LaurentSeries (AlgebraicClosure ℚ))) h)
  intro P hP hP1 hϖP hgP
  have hqP : ((q : ℕ) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∉ P := by
    intro hmem
    rw [hqR] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact hϖP (hP.mem_of_pow_mem eK h)
    · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h hκε)
  have hCle := L2H.jIntegralClosure_le red a K hIC
  letI algC : Algebra ↥(jIntegralClosure (1 * q) A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := (Subring.inclusion hCle).toAlgebra
  haveI hLocC := L2H.isLocalization_C red a K hCle
  have h𝔭1 : (P.under ↥(jIntegralClosure (1 * q) A K)).height = 1 := by
    rw [IsLocalization.height_under (L2H.nodeDenomC (q := q) red a K) P]
    exact hP1
  have hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ P.under ↥(jIntegralClosure (1 * q) A K) := by
    intro hmem
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem
    exact hqP hmem
  have h𝔭S : ∀ s : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0 →
      ∀ hs : modularEval (1 * q) (coeffSubring A K) s ∈ jIntegralClosure (1 * q) A K,
        (⟨_, hs⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ P.under ↥(jIntegralClosure (1 * q) A K) := by
    intro s hs hsC hmem
    rw [Ideal.under_def, Ideal.mem_comap] at hmem
    have heq : algebraMap ↥(jIntegralClosure (1 * q) A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ⟨_, hsC⟩ = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) s := Subtype.ext rfl
    rw [heq] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
      (isUnit_modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) hs))
  obtain ⟨W, hWc, hiff⟩ :=
    ModularCurve.exists_place_centred_node_of_height_one_of_natCast_notMem red a K (P.under ↥(jIntegralClosure (1 * q) A K)) h𝔭1 hq𝔭 h𝔭S
  have hord : W.ord gB = 0 := hford W hWc
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥W.toValuationSubring
  obtain ⟨uu, huu⟩ := W.exists_unit_mul_zpow (inv_ne_zero hgB0) hπ
  simp only [Place.ord_inv, hord, neg_zero, zpow_zero, mul_one] at huu
  have hginv : gB⁻¹ ∈ W.toValuationSubring := by
    rw [huu]; exact (uu : ↥W.toValuationSubring).2
  have hcoe : ((gB⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = (g : LaurentSeries (AlgebraicClosure ℚ))⁻¹ := rfl
  have hgFO : ((gB⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K := by
    rw [hcoe]
    exact (fieldOver (1 * q) K).inv_mem (L2H.coe_mem_fieldOver red a K g)
  obtain ⟨r, s, hs𝔭, hrs⟩ := (hiff (gB⁻¹) hgFO).mpr hginv
  rw [hcoe] at hrs
  apply hs𝔭
  rw [Ideal.under_def, Ideal.mem_comap]
  have hsr : algebraMap ↥(jIntegralClosure (1 * q) A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) s = g * algebraMap ↥(jIntegralClosure (1 * q) A K) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) r := by
    apply Subtype.ext
    show (s : LaurentSeries (AlgebraicClosure ℚ)) = (g : LaurentSeries (AlgebraicClosure ℚ)) * (r : LaurentSeries (AlgebraicClosure ℚ))
    rw [← hrs, ← mul_assoc, mul_inv_cancel₀ hg0L, one_mul ((s : ↥(jIntegralClosure (1 * q) A K)) : LaurentSeries (AlgebraicClosure ℚ))]
  rw [hsr]
  exact P.mul_mem_right _ hgP

end L2S

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (heK1 : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (jWidth a * eK) * w)
    (hmax : ∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
        IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
          Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'})
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'})
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
    (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hg0 : g ≠ 0)
    (hgF : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q))
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord (⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : modularFunctionFieldBar (1 * q)) = 0) :
    ∃ (l i j : ℕ) (u : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), IsUnit u ∧
      g = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ l *
        H' ^ i * G' ^ j * u := by

  obtain ⟨hNoeth, hLocal, -, -⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
      red a K x hx ϖ hϖ
  haveI := hNoeth
  haveI := hLocal
  haveI hFact : Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K))
      ≤ RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
    ⟨fun s hs => (RingHom.mem_ker).mpr
      (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s
        ((RingHom.mem_ker).mp hs))⟩
  have hmax' : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'} := hmax

  have hloc : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'} ≠ ⊤ := by
    rw [← hmax']
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have he : 1 ≤ jWidth a * eK := Nat.succ_le_of_lt (Nat.mul_pos (jWidth_pos a) heK1)

  have hIC : IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    L2S.isIntegrallyClosed_nodeRing red a K x hx ϖ hϖ (jWidth a * eK) he G' H' w hw hGH hmax' hpr1 hpr2 hnm1 hnm2
  haveI := hIC

  have BR1 := L2S.branchReading red a ha2 K ϖ hϖ G' H' hpr1 hnm1 hsp1 hsp2

  have hHart : ∀ z : FractionRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)),
      (∀ (p : Ideal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) [p.IsPrime], p.height = 1 →
        ∃ r s : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)), s ∉ p ∧ z * algebraMap _ _ s = algebraMap _ _ r) →
      ∃ r : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)), algebraMap _ _ r = z :=
    fun z hz => IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one (FractionRing _) z hz

  have HOR := L2S.notMem_of_height_one red a K ϖ eK ε hε hqϖ hIC g hg0 hgF hford
  obtain ⟨n, hgn⟩ := L2G.exists_dvd_pow_of_forall_height_one hg0 HOR
  obtain ⟨l, i, j, u, hu, hEq⟩ :=
    L2G.monomial_of_dvd_pow he hw hGH hpr1 hpr2 hnm1 hnm2 hloc BR1 hHart n g hg0 hgn
  exact ⟨l, j, i, u, hu, by rw [hEq]; ring⟩

end S_ModularCurve_NodeLocalized_exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation (solution)
