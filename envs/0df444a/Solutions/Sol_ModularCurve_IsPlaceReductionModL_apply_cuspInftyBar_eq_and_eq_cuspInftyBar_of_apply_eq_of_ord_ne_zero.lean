-- Prove2me | solution 1 for ModularCurve.IsPlaceReductionModL.apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/121d5b39-36c1-56cf-9b84-7242915b3260

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_ModularCurve_IsPlaceReductionModL_coordinate_clauses
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_of_isCusp_of_ord_jqN_eq_mul_ord_jq_of_neZero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsPlaceReductionModL_apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"

set_option autoImplicit false

open AlgebraicCurve

namespace K1aAux

open Classical in
theorem mapDomain_apply_eq_sum {α β : Type*} (r : α → β) (D : α →₀ ℤ) (Q : β) :
    Finsupp.mapDomain r D Q = ∑ a ∈ D.support with r a = Q, D a := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : r a = Q
  · rw [if_pos h, h, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_apply, if_neg h]

theorem eq_neg_one_and_unique_of_sum_eq_neg_one {α : Type*} (s : Finset α) (f : α → ℤ)
    (hf : ∀ a ∈ s, f a ≤ 0) (hs : ∑ a ∈ s, f a = -1) {a : α} (ha : a ∈ s) (hfa : f a ≠ 0) :
    f a = -1 ∧ ∀ b ∈ s, f b ≠ 0 → b = a := by
  classical
  rw [← Finset.add_sum_erase s f ha] at hs
  have hrest : ∑ x ∈ s.erase a, f x ≤ 0 :=
    Finset.sum_nonpos fun x hx => hf x (Finset.mem_of_mem_erase hx)
  have hfa' : f a ≤ 0 := hf a ha
  have h1 : f a = -1 := by omega
  refine ⟨h1, fun b hb hfb => ?_⟩
  by_contra hba
  have h0 : ∑ x ∈ s.erase a, f x = 0 := by omega
  rw [Finset.sum_eq_zero_iff_of_nonpos (fun x hx => hf x (Finset.mem_of_mem_erase hx))] at h0
  exact hfb (h0 b (Finset.mem_erase.mpr ⟨hba, hb⟩))

theorem isCusp_of_ord_neg {K E : Type*} {_ : Field K} {_ : Field E} {_ : Algebra K E}
    (j : E) (v : Place K E) (h : v.ord j < 0) : ModularCurve.IsCusp j v := fun hmem => by
  have := Place.ord_nonneg_of_mem v hmem
  omega

theorem core {K F k Fb : Type*} {_ : Field K} {_ : Field F} {_ : Algebra K F} {_ : Field k} {_ : Field Fb}
    {_ : Algebra k Fb}
    (r : Place K F → Place k Fb) (P : Place k Fb) (m : ℤ)
    (j jN : F) (jb jNb : Fb)
    (hQj : P.ord jb = -1) (hQjN : P.ord jNb = -m)
    (hAj : ∀ w, r w = P → w.ord j ≤ 0) (hAjN : ∀ w, r w = P → w.ord jN ≤ 0)
    (Dj DjN : Divisor K F) (hDj : ∀ v, Dj v = v.ord j) (hDjN : ∀ v, DjN v = v.ord jN)
    (hpj : Finsupp.mapDomain r Dj P = P.ord jb) (hpjN : Finsupp.mapDomain r DjN P = P.ord jNb)
    (hR6 : ∀ w, r w = P → w.ord j = 0 → 0 ≤ w.ord jN) :
    (∃ w, r w = P ∧ w.ord j ≠ 0) ∧
    ∀ w, r w = P → w.ord j ≠ 0 →
      ModularCurve.IsCusp j w ∧ w.ord jN = m * w.ord j ∧ ∀ w', r w' = P → w'.ord j ≠ 0 → w' = w := by
  classical
  rw [mapDomain_apply_eq_sum, hQj] at hpj
  rw [mapDomain_apply_eq_sum, hQjN] at hpjN
  have hex : ∃ w, r w = P ∧ w.ord j ≠ 0 := by
    obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Dj.support.filter fun a => r a = P) (f := Dj) (by rw [hpj]; decide)
    exact ⟨a, (Finset.mem_filter.mp ha).2, show a.ord j ≠ 0 by rw [← hDj]; exact hne⟩
  refine ⟨hex, fun w hw hne => ?_⟩
  have hle : ∀ a ∈ Dj.support.filter (fun a => r a = P), Dj a ≤ 0 := fun a ha => by
    rw [hDj]; exact hAj a (Finset.mem_filter.mp ha).2
  have hmem : w ∈ Dj.support.filter (fun a => r a = P) :=
    Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [hDj]; exact hne), hw⟩
  obtain ⟨hm1, huniq⟩ :=
    eq_neg_one_and_unique_of_sum_eq_neg_one _ Dj hle hpj hmem (show Dj w ≠ 0 by rw [hDj]; exact hne)
  have hordj : w.ord j = -1 := by rw [← hDj]; exact hm1
  have huniq' : ∀ w', r w' = P → w'.ord j ≠ 0 → w' = w := fun w' hw' hne' =>
    huniq w' (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [hDj]; exact hne'), hw'⟩)
      (show Dj w' ≠ 0 by rw [hDj]; exact hne')
  refine ⟨isCusp_of_ord_neg j w (by omega), ?_, huniq'⟩
  suffices hN : w.ord jN = -m by rw [hN, hordj]; ring
  have hothers : ∀ w', r w' = P → w' ≠ w → DjN w' = 0 := by
    intro w' hw' hne'
    have h0 : w'.ord j = 0 := by
      by_contra h
      exact hne' (huniq' w' hw' h)
    rw [hDjN]
    exact le_antisymm (hAjN w' hw') (hR6 w' hw' h0)
  rw [Finset.sum_eq_single w (fun b hb hbw => hothers b (Finset.mem_filter.mp hb).2 hbw)
    (fun hw' => ?_)] at hpjN
  · rw [← hDjN]; exact hpjN
  · by_contra hD
    exact hw' (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hD, hw⟩)

theorem eq_qInftyPlaceMod (K : Type*) [Field K] {F : IntermediateField K (LaurentSeries K)}
    (hF : ModularCurve.jqModC K ∈ F) (P : Place K F)
    (hP : ∀ f : F, f ∈ P.toValuationSubring ↔ 0 ≤ ((f : F) : LaurentSeries K).order) :
    P = ModularCurve.qInftyPlaceMod K hF := by
  apply Place.ext
  ext f
  rw [hP f, ModularCurve.qInftyPlaceMod_toValuationSubring, ModularCurve.mem_qIntegersBar_iff]
  rfl

noncomputable section Modular

open ModularCurve IsLocalRing HahnSeries

set_option synthInstance.maxHeartbeats 1600000

abbrev jF (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

abbrev jNF (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

abbrev jb (k : Type*) [Field k] (N : ℕ) [NeZero N] : modularFunctionFieldFullC k N :=
  ⟨jqModC k, jqModC_mem_full k N⟩

abbrev jNb (k : Type*) [Field k] (N : ℕ) [NeZero N] : modularFunctionFieldFullC k N :=
  ⟨jqNModC k N, modularFunctionFieldC_le_full k N (jqNModC_mem k N)⟩

theorem coe_jF (N : ℕ) [NeZero N] :
    ((jF N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
  coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem coe_jNF (N : ℕ) [NeZero N] :
    ((jNF N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqNModC (AlgebraicClosure ℚ) N :=
  coeffMap_jqNModC (algebraMap ℚ (AlgebraicClosure ℚ)) N

theorem jF_ne_zero (N : ℕ) [NeZero N] : jF N ≠ 0 := fun h =>
  jqModC_ne_zero_def (AlgebraicClosure ℚ) (by rw [← coe_jF N, h]; rfl)

theorem jNF_ne_zero (N : ℕ) [NeZero N] : jNF N ≠ 0 := fun h =>
  jqNModC_ne_zero (AlgebraicClosure ℚ) N (by rw [← coe_jNF N, h]; rfl)

theorem jb_ne_zero (k : Type*) [Field k] (N : ℕ) [NeZero N] : jb k N ≠ 0 := fun h =>
  jqModC_ne_zero_def k (congrArg Subtype.val h)

theorem jNb_ne_zero (k : Type*) [Field k] (N : ℕ) [NeZero N] : jNb k N ≠ 0 := fun h =>
  jqNModC_ne_zero k N (congrArg Subtype.val h)

theorem jNF_mem_of_jF_mem (N : ℕ) [NeZero N]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hj : jF N ∈ w.toValuationSubring) : jNF N ∈ w.toValuationSubring := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N

  have hrel : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jF N)).toRingHom (jNF N) = 0 := by
    apply (algebraMap (modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))).injective
    rw [Polynomial.hom_eval₂, map_zero]
    have h0 := congrArg (coeffEmb (AlgebraicClosure ℚ)) data.eval_eq_zero
    rw [Polynomial.hom_eval₂, map_zero] at h0
    have hhom : (algebraMap (modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))).comp
        (Polynomial.aeval (R := ℤ) (jF N)).toRingHom =
        (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
    rw [hhom]
    exact h0

  have hint : IsIntegral w.toValuationSubring (jNF N) := by
    refine ⟨data.Φ.map (Polynomial.aeval (R := ℤ) (⟨jF N, hj⟩ : w.toValuationSubring)).toRingHom,
      data.monic.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hhom : (algebraMap w.toValuationSubring (modularFunctionFieldBar N)).comp
        (Polynomial.aeval (R := ℤ) (⟨jF N, hj⟩ : w.toValuationSubring)).toRingHom =
        (Polynomial.aeval (R := ℤ) (jF N)).toRingHom := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
    rw [hhom]
    exact hrel
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.toValuationSubring)
    (K := modularFunctionFieldBar N)).mp hint
  rw [← hy]
  exact y.2

theorem transfer (N : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N))
    (hr : IsPlaceReductionModL A N r) (y : LaurentSeries A)
    (e : modularFunctionFieldBar N) (eb : modularFunctionFieldFullC (ResidueField A) N)
    (he : coeffMap A.subtype y = (e : LaurentSeries (AlgebraicClosure ℚ)))
    (heb : coeffMap (residue A) y = (eb : LaurentSeries (ResidueField A)))
    (hne : eb ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ P, D P = P.ord e) :
    ∀ Q, Finsupp.mapDomain r D Q = Q.ord eb := by
  have hy : coeffMap A.subtype y ∈
      laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) := by
    rw [he]; exact e.2
  have hyk : coeffMap (residue A) y ∈ modularFunctionFieldFullC (ResidueField A) N := by
    rw [heb]; exact eb.2
  have h1 : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) = e := Subtype.ext he
  have h2 : (⟨coeffMap (residue A) y, hyk⟩ : modularFunctionFieldFullC (ResidueField A) N) = eb :=
    Subtype.ext heb
  have hne' : coeffMap (residue A) y ≠ 0 := by
    rw [heb]
    exact fun h => hne (ZeroMemClass.coe_eq_zero.mp h)
  intro Q
  have := hr.2 y hy hyk hne' D (fun P => by rw [h1]; exact hD P) Q
  rwa [h2] at this

set_option maxHeartbeats 6400000 in

theorem main (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr : IsPlaceReductionModL A N r)
    (Pinf : Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hPinf : ∀ f : modularFunctionFieldFullC (ResidueField ↥A) N,
      f ∈ Pinf.toValuationSubring ↔
        0 ≤ ((f : modularFunctionFieldFullC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)).order) :
    r (cuspInftyBar N) = Pinf ∧
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), r w = Pinf →
      w.ord (jF N) ≠ 0 → w = cuspInftyBar N := by
  classical

  have hP : Pinf = qInftyPlaceMod (ResidueField ↥A) (jqModC_mem_full (ResidueField ↥A) N) :=
    eq_qInftyPlaceMod (ResidueField ↥A) (jqModC_mem_full (ResidueField ↥A) N) Pinf hPinf
  have hQj : Pinf.ord (jb (ResidueField ↥A) N) = -1 := by
    rw [hP, ord_qInftyPlaceMod]
    exact order_jqModC_def (ResidueField ↥A)
  have hQjN : Pinf.ord (jNb (ResidueField ↥A) N) = -(N : ℤ) := by
    rw [hP, ord_qInftyPlaceMod]
    exact order_jqNModC (ResidueField ↥A) N

  obtain ⟨hci, -, hciii, -⟩ := ModularCurve.IsPlaceReductionModL.coordinate_clauses N p hpN A hA r hr
  have hAj : ∀ w, r w = Pinf → w.ord (jF N) ≤ 0 := by
    intro w hw
    by_contra hlt
    push Not at hlt
    have h := hci w 0 (by rw [ZeroMemClass.coe_zero, map_zero, sub_zero]; exact hlt)
    rw [map_zero, map_zero, sub_zero, hw] at h
    have h' : (0 : ℤ) < -1 := by rw [← hQj]; exact h
    omega
  have hAjN : ∀ w, r w = Pinf → w.ord (jNF N) ≤ 0 := by
    intro w hw
    by_contra hlt
    push Not at hlt
    have h := hciii w 0 (by rw [ZeroMemClass.coe_zero, map_zero, sub_zero]; exact hlt)
    rw [map_zero, map_zero, sub_zero, hw] at h
    have h' : (0 : ℤ) < -(N : ℤ) := by rw [← hQjN]; exact h
    omega

  obtain ⟨Dj, hDj, -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor _ (jF_ne_zero N)
  obtain ⟨DjN, hDjN, -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor _ (jNF_ne_zero N)
  have hpj : Finsupp.mapDomain r Dj Pinf = Pinf.ord (jb (ResidueField ↥A) N) :=
    transfer N A r hr (jqModC A) (jF N) (jb (ResidueField ↥A) N)
      (by rw [coe_jF, coeffMap_jqModC]) (coeffMap_jqModC _) (jb_ne_zero _ N) Dj hDj Pinf
  have hpjN : Finsupp.mapDomain r DjN Pinf = Pinf.ord (jNb (ResidueField ↥A) N) :=
    transfer N A r hr (jqNModC A N) (jNF N) (jNb (ResidueField ↥A) N)
      (by rw [coe_jNF, coeffMap_jqNModC]) (coeffMap_jqNModC _ N) (jNb_ne_zero _ N) DjN hDjN Pinf

  have hR6 : ∀ w, r w = Pinf → w.ord (jF N) = 0 → 0 ≤ w.ord (jNF N) := fun w _ h0 =>
    Place.ord_nonneg_of_mem w
      (jNF_mem_of_jF_mem N w (Place.mem_of_ord_nonneg w (jF_ne_zero N) (le_of_eq h0.symm)))

  obtain ⟨⟨w₀, hw₀, hne₀⟩, hcount⟩ :=
    core r Pinf (N : ℤ) (jF N) (jNF N) (jb (ResidueField ↥A) N) (jNb (ResidueField ↥A) N)
      hQj hQjN hAj hAjN Dj DjN hDj hDjN hpj hpjN hR6

  have hC : ∀ w, r w = Pinf → w.ord (jF N) ≠ 0 → w = cuspInftyBar N := by
    intro w hw hne
    obtain ⟨hcusp, hord, -⟩ := hcount w hw hne
    exact eq_cuspInftyBar_of_isCusp_of_ord_jqN_eq_mul_ord_jq_of_neZero N w hcusp hord

  refine ⟨?_, hC⟩
  have hw₀eq : w₀ = cuspInftyBar N := hC w₀ hw₀ hne₀
  subst hw₀eq
  exact hw₀

end Modular

end K1aAux

open ModularCurve AlgebraicCurve IsLocalRing

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr : IsPlaceReductionModL A N r)

    (Pinf : Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hPinf : ∀ f : modularFunctionFieldFullC (ResidueField ↥A) N,
      f ∈ Pinf.toValuationSubring ↔ 0 ≤ ((f : modularFunctionFieldFullC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)).order) :
    r (cuspInftyBar N) = Pinf ∧
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), r w = Pinf →
      w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) ≠ 0 → w = cuspInftyBar N :=
  K1aAux.main N p hpN A hA r hr Pinf hPinf

#print axioms solution

end S_ModularCurve_IsPlaceReductionModL_apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero
end P2MW
export P2MW.S_ModularCurve_IsPlaceReductionModL_apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero (solution)
