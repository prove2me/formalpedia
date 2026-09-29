-- Prove2me | solution 1 for ModularCurve.JZero.chordVec_ne_zero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4de8f67d-af9b-59c2-bd89-5519c7d8048c

import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_genus_riemannIndex_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_constantsAreBase_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_chordVec_ne_zero_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.jqNModC_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option Elab.async false
set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve KaehlerDifferential

namespace SepPen

section EvalGlue

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mem_vr_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

private theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

private theorem evalAt_smul (v : Place K F) (hv : v.IsRational) (c : K) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.evalAt (c • f) = c * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul hv (v.algebraMap_mem' c) hf, v.evalAt_algebraMap]

private theorem evalAt_finsetSum (v : Place K F) (hv : v.IsRational) {ι : Type*}
    (t : Finset ι) (f : ι → F) (h : ∀ i ∈ t, f i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ t, f i) = ∑ i ∈ t, v.evalAt (f i) := by
  induction t using Finset.cons_induction with
  | empty => simpa using evalAt_zero v
  | cons a t ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        evalAt_add v hv (h a (Finset.mem_cons_self a t))
          (sum_mem fun i hi => h i (Finset.mem_cons_of_mem hi)),
        ih fun i hi => h i (Finset.mem_cons_of_mem hi)]

private theorem evalAt_eq_zero_of_ord_pos (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ≠ 0) (h : 0 < v.ord f) : v.evalAt f = 0 := by
  have hmem : f ∈ v.toValuationSubring := mem_vr_of_ord_nonneg v hf h.le
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hmem, map_zero]
  by_contra hres
  have hu : IsUnit (⟨f, hmem⟩ : v.toValuationSubring) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have hval : v.adicValuation f = 1 := (v.adicValuation_coe_eq_one_iff ⟨f, hmem⟩).mpr hu
  have hord0 : v.ord f = 0 := by rw [Place.ord, hval]; simp
  omega

private theorem ord_algebraMap_eq_zero (v : Place K F) {c : K} (hc : c ≠ 0) :
    v.ord (algebraMap K F c) = 0 := by
  have hmapne : algebraMap K F c ≠ 0 := fun h =>
    hc ((algebraMap K F).injective (by rw [h, map_zero]))
  have hof : ∀ d : K, algebraMap K F d ≠ 0 → 0 ≤ v.ord (algebraMap K F d) := by
    intro d hd
    have hle : v.adicValuation (algebraMap K F d) ≤ WithZero.exp ((0 : Divisor K F) v) := by
      rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
      exact v.adicValuation_algebraMap_le_one d
    rcases (v.adicValuation_le_exp_iff).mp hle with h0 | h0
    · exact absurd h0 hd
    · simpa using h0
  have h1 : 0 ≤ v.ord (algebraMap K F c) := hof c hmapne
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := hof c⁻¹ (by
    rw [map_inv₀]; exact inv_ne_zero hmapne)
  rw [map_inv₀, v.ord_inv] at h2
  omega

end EvalGlue

section RRGlue

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem degree_nonneg {D : Divisor K F} (hD : 0 ≤ D) : 0 ≤ Divisor.degree D := by
  have hrw : Divisor.degree D = D.sum fun v n => n * (v.deg : ℤ) := by
    unfold Divisor.degree
    rw [Finsupp.liftAddHom_apply]
    rfl
  rw [hrw]
  unfold Finsupp.sum
  refine Finset.sum_nonneg fun x _ => mul_nonneg ?_ (by positivity)
  simpa using Finsupp.le_def.mp hD x

private theorem lSpace_eq_bot_of_degree_neg [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : Divisor.degree D < 0) : riemannRochSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hfne
  rcases mem_lSpace_iff_ord.mp hf with h0 | hord
  · exact hfne h0
  obtain ⟨P, hPord, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hfne
  have hDP : (0 : Divisor K F) ≤ D + P := by
    refine Finsupp.le_def.mpr fun x => ?_
    have hx := hord x
    rw [Finsupp.add_apply, hPord x]
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega
  have hnn := degree_nonneg hDP
  rw [map_add, hPdeg] at hnn
  omega

private theorem ell_eq_zero_of_degree_neg [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : Divisor.degree D < 0) : ell D = 0 := by
  have hb : riemannRochSpace D = (⊥ : Submodule K F) := lSpace_eq_bot_of_degree_neg hD
  calc ell D = Module.finrank K (riemannRochSpace (K := K) (F := F) D) := rfl
    _ = Module.finrank K (⊥ : Submodule K F) := by rw [hb]
    _ = 0 := finrank_bot K F

private theorem sub_single_le (D : Divisor K F) (x : Place K F) :
    D - Finsupp.single x (1 : ℤ) ≤ D := by
  classical
  refine Finsupp.le_def.mpr fun a => ?_
  rw [Finsupp.sub_apply, Finsupp.single_apply]
  split <;> omega

private theorem ord_pin {D : Divisor K F} {x : Place K F} {u : F}
    (hu : u ∈ riemannRochSpace D)
    (hnot : u ∉ riemannRochSpace (D - Finsupp.single x (1 : ℤ))) :
    u ≠ 0 ∧ x.ord u = -D x := by
  classical
  have hune : u ≠ 0 := by rintro rfl; exact hnot (Submodule.zero_mem _)
  refine ⟨hune, ?_⟩
  rcases mem_lSpace_iff_ord.mp hu with h0 | hbound
  · exact absurd h0 hune
  have hge : -D x ≤ x.ord u := hbound x
  by_contra hne'
  apply hnot
  refine mem_lSpace_iff_ord.mpr (Or.inr fun y => ?_)
  rw [Finsupp.sub_apply, Finsupp.single_apply]
  by_cases hyx : x = y
  · subst hyx
    rw [if_pos rfl]
    have : -D x < x.ord u := lt_of_le_of_ne hge fun h => hne' h.symm
    omega
  · rw [if_neg hyx, sub_zero]
    exact hbound y

end RRGlue

section Bridge

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

private def adeleSubalg [HasPrincipalDivisors K F] : Subalgebra F (Place K F → F) where
  carrier := adeleSpace K F
  add_mem' ha hb := (adeleSpace K F).add_mem ha hb
  zero_mem' := (adeleSpace K F).zero_mem
  mul_mem' := by
    intro a b ha hb
    obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp ha
    obtain ⟨E, hE⟩ := mem_adeleSpace_iff.mp hb
    refine adeleBdd_le_adeleSpace (D := D + E) fun x => ?_
    rw [Pi.mul_apply, map_mul, Finsupp.add_apply, WithZero.exp_add]
    exact mul_le_mul' (hD x) (hE x)
  one_mem' := by
    refine adeleBdd_le_adeleSpace (D := 0) fun x => ?_
    rw [Pi.one_apply, map_one, Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  algebraMap_mem' c := diagonal_mem_adeleSpace c

private theorem mem_adeleSpace_iff_mem_repartitions [HasPrincipalDivisors K F]
    (α : Place K F → F) :
    α ∈ adeleSpace K F ↔ α ∈ repartitions K F := by
  constructor
  · intro hα
    obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
    exact mem_repartitions_of_forall_le_exp D α hD
  · intro hα
    have hle : repartitions K F ≤ adeleSubalg K F := by
      refine Algebra.adjoin_le ?_
      intro β hβ
      classical
      set S : Finset (Place K F) := hβ.toFinset with hSdef
      have hSmem : ∀ y : Place K F, y ∈ S ↔ ¬y.adicValuation (β y) ≤ 1 := fun y => by
        rw [hSdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      set D : Divisor K F := Finsupp.onFinset S
        (fun y => if y ∈ S then -(y.ord (β y)) else 0)
        (fun y hy => by by_contra hyS; rw [if_neg hyS] at hy; exact hy rfl)
        with hDdef
      have hDapp : ∀ y : Place K F, D y = if y ∈ S then -(y.ord (β y)) else 0 := fun y => rfl
      refine adeleBdd_le_adeleSpace (D := D) fun y => ?_
      by_cases hy : y ∈ S
      · have hβy : β y ≠ 0 := by
          intro h0
          exact (hSmem y).mp hy (by rw [h0]; simp)
        rw [hDapp y, if_pos hy]
        refine le_of_eq ?_
        rw [show y.adicValuation (β y) = WithZero.exp (-y.ord (β y)) by
          rw [Place.ord, neg_neg, WithZero.exp_log (y.adicValuation_ne_zero hβy)]]
      · rw [hDapp y, if_neg hy, WithZero.exp_zero]
        exact not_not.mp fun hc => hy ((hSmem y).mpr hc)
    exact hle hα

private def adeleRepartEquiv [HasPrincipalDivisors K F] :
    ↥(adeleSpace K F) ≃ₗ[K] ↥(repartitions K F) where
  toFun x := ⟨(x : Place K F → F), (mem_adeleSpace_iff_mem_repartitions K F _).mp x.2⟩
  invFun y := ⟨(y : Place K F → F), (mem_adeleSpace_iff_mem_repartitions K F _).mpr y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem map_adeleBddPrincipal_zero [HasPrincipalDivisors K F] :
    (adeleBddPrincipal K F (0 : Divisor K F)).map
        (adeleRepartEquiv K F : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F))
      = repartitionsOf (0 : Divisor K F) ⊔ principalRepartitions K F := by
  have h1 : ((adeleBdd (0 : Divisor K F)).comap (adeleSpace K F).subtype).map
      (adeleRepartEquiv K F : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F))
      = repartitionsOf (0 : Divisor K F) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact fun z => hy z
    · intro hx
      exact ⟨(adeleRepartEquiv K F).symm x, fun z => hx z,
        (adeleRepartEquiv K F).apply_symm_apply x⟩
  have h2 : ((globalSub K F).comap (adeleSpace K F).subtype).map
      (adeleRepartEquiv K F : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F))
      = principalRepartitions K F := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨f, hf⟩ := LinearMap.mem_range.mp hy
      refine mem_principalRepartitions_iff.mpr ⟨f, ?_⟩
      show (y : Place K F → F) = fun _ => f
      rw [← hf]
      funext z
      exact diagonalHom_apply f z
    · intro hx
      obtain ⟨f, hf⟩ := mem_principalRepartitions_iff.mp hx
      refine ⟨(adeleRepartEquiv K F).symm x, LinearMap.mem_range.mpr ⟨f, ?_⟩,
        (adeleRepartEquiv K F).apply_symm_apply x⟩
      funext z
      rw [diagonalHom_apply]
      exact (congrFun hf z).symm
  rw [Submodule.map_sup, h1, h2]

private theorem indexOfSpecialty_zero_eq_genusFF [HasPrincipalDivisors K F] :
    indexOfSpecialty (K := K) (F := F) (0 : Divisor K F) = genusFF K F := by
  rw [indexOfSpecialty_eq]
  exact LinearEquiv.finrank_eq
    (Submodule.Quotient.equiv _ _ (adeleRepartEquiv K F) (map_adeleBddPrincipal_zero K F))

end Bridge

section Pivot

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

private theorem pivot_min {r : ℕ} (s : Fin r → F) (x : Place (AlgebraicClosure ℚ) F)
    (hr : 0 < r) (i : Fin r) :
    x.ord (s (pivotIndex s x hr)) ≤ x.ord (s i) := by
  have hex : ∃ k : Fin r, ∀ j : Fin r, x.ord (s k) ≤ x.ord (s j) := by
    obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (fun i => x.ord (s i))
      ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    exact ⟨k, fun j => hk j (Finset.mem_univ j)⟩
  unfold pivotIndex
  rw [dif_pos hex]
  exact Classical.choose_spec hex i

private theorem evalVec_eq {r : ℕ} (s : Fin r → F) (x : Place (AlgebraicClosure ℚ) F)
    (hr : 0 < r) (i : Fin r) :
    evalVec s x i = x.evalAt (s i * (s (pivotIndex s x hr))⁻¹) := by
  unfold evalVec
  rw [dif_pos hr]

private theorem evalVec_pivot_eq_one {r : ℕ} (s : Fin r → F)
    (x : Place (AlgebraicClosure ℚ) F) (hr : 0 < r)
    (hne : s (pivotIndex s x hr) ≠ 0) :
    evalVec s x (pivotIndex s x hr) = 1 := by
  rw [evalVec_eq s x hr, mul_inv_cancel₀ hne, Place.evalAt_one]

private theorem le_ord_of_mem_span {r : ℕ} (s : Fin r → F)
    (x : Place (AlgebraicClosure ℚ) F) {μ : ℤ} (hμ : ∀ i, μ ≤ x.ord (s i)) {u : F}
    (hu : u ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s)) (hune : u ≠ 0) :
    μ ≤ x.ord u := by
  have key : ∀ z, z ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) →
      z ≠ 0 → μ ≤ x.ord z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact fun _ => hμ i
    | zero => exact fun h => absurd rfl h
    | add y z _ _ hy hz =>
        intro hyz
        rcases eq_or_ne y 0 with rfl | hy0
        · rw [zero_add] at hyz ⊢
          exact hz hyz
        rcases eq_or_ne z 0 with rfl | hz0
        · rw [add_zero] at hyz ⊢
          exact hy hyz
        exact le_trans (le_min (hy hy0) (hz hz0)) (x.min_ord_le_ord_add hy0 hz0 hyz)
    | smul c y _ hy =>
        intro hcy
        have hc0 : c ≠ 0 := fun h => hcy (by rw [h, zero_smul])
        have hy0 : y ≠ 0 := fun h => hcy (by rw [h, smul_zero])
        have hmapne : algebraMap (AlgebraicClosure ℚ) F c ≠ 0 := fun h =>
          hc0 ((algebraMap (AlgebraicClosure ℚ) F).injective (by rw [h, map_zero]))
        rw [Algebra.smul_def, x.ord_mul hmapne hy0, ord_algebraMap_eq_zero x hc0, zero_add]
        exact hy hy0
  exact key u hu hune

private theorem evalAt_linComb {r : ℕ} (s : Fin r → F) (hsne : ∀ i, s i ≠ 0)
    (x : Place (AlgebraicClosure ℚ) F) (hx : x.IsRational) (hr : 0 < r)
    (c : Fin r → AlgebraicClosure ℚ) :
    x.evalAt ((∑ i, c i • s i) * (s (pivotIndex s x hr))⁻¹)
      = ∑ i, c i * evalVec s x i := by
  have hkne : s (pivotIndex s x hr) ≠ 0 := hsne _
  have hmem : ∀ i : Fin r, s i * (s (pivotIndex s x hr))⁻¹ ∈ x.toValuationSubring := by
    intro i
    refine mem_vr_of_ord_nonneg x (mul_ne_zero (hsne i) (inv_ne_zero hkne)) ?_
    rw [x.ord_mul (hsne i) (inv_ne_zero hkne), x.ord_inv]
    have := pivot_min s x hr i
    omega
  rw [Finset.sum_mul,
    evalAt_finsetSum x hx Finset.univ (fun i => c i • s i * (s (pivotIndex s x hr))⁻¹)
      (fun i _ => by
        try dsimp only
        rw [smul_mul_assoc, Algebra.smul_def]
        exact mul_mem (x.algebraMap_mem' _) (hmem i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, evalAt_smul x hx (c i) (hmem i), evalVec_eq s x hr]

end Pivot

end SepPen

open SepPen

set_option maxHeartbeats 3200000 in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hvw : v ≠ w) :
    chordVec s v w ≠ 0 := by
  classical

  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI := ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar N
  haveI := ModularCurve.essFiniteType_modularFunctionFieldBar N
  haveI : ∀ vv : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), vv.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hdeg1 : ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), x.deg = 1 :=
    ModularCurve.deg_eq_one_modularFunctionFieldBar N
  have hrat : ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), x.IsRational :=
    fun x => x.isRational_iff_deg_eq_one.mpr (hdeg1 x)

  obtain ⟨γ, hγ⟩ := ModularCurve.exists_genus_riemannIndex_modularFunctionFieldBar N
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[↥(modularFunctionFieldBar N)⁄AlgebraicClosure ℚ])
  have hRR := fun D => ModularCurve.functionFieldRiemannRoch_modularFunctionFieldBar N
    (ω := ω) hω D

  obtain ⟨g, hgdef⟩ : ∃ n : ℕ, genus (AlgebraicClosure ℚ) (modularFunctionFieldBar N) = n :=
    ⟨_, rfl⟩
  obtain ⟨Kω, hKωdef⟩ : ∃ D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      canonicalDivisorOf hω = D₀ := ⟨_, rfl⟩
  obtain ⟨gFF, hgFFdef⟩ : ∃ n : ℕ,
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) = n := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      embDivisor N = D₀ := ⟨_, rfl⟩
  simp only [hgdef, hKωdef] at hRR

  have hdegK : Divisor.degree Kω = 2 * (g : ℤ) - 2 := by
    have h1 := hRR 0
    have h2 := hRR Kω
    rw [sub_zero] at h1
    rw [sub_self] at h2
    rw [map_zero] at h1
    linarith

  have hd1 : ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Divisor.degree (Finsupp.single x (1 : ℤ)) = 1 := fun x => by
    rw [Divisor.degree_single, hdeg1 x]
    simp

  have hell0 : ell (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = 1 :=
    ell_zero_eq_one_of_constantsAreBase (ModularCurve.constantsAreBase_modularFunctionFieldBar N)

  have hγFF : γ = (gFF : ℤ) := by
    have h0 := (hγ 0).2
    rw [SepPen.indexOfSpecialty_zero_eq_genusFF, hgFFdef, hell0, map_zero] at h0
    push_cast at h0
    linarith

  have hgγ : (g : ℤ) ≤ γ := by
    set D0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      (2 * (g : ℤ)) • Finsupp.single (cuspInftyBar N) (1 : ℤ) with hD0
    have hdegD0 : Divisor.degree D0 = 2 * (g : ℤ) := by
      rw [hD0, map_zsmul, hd1, smul_eq_mul, mul_one]
    have hKD0 : Divisor.degree (Kω - D0) < 0 := by
      rw [map_sub, hdegK, hdegD0]
      omega
    have hellK0 : ell (Kω - D0) = 0 := ell_eq_zero_of_degree_neg hKD0
    have hRRD0 := hRR D0
    rw [hellK0] at hRRD0
    have hiD0 := (hγ D0).2
    have hnn : (0 : ℤ) ≤ (indexOfSpecialty D0 : ℤ) := Int.natCast_nonneg _
    rw [hdegD0] at hRRD0 hiD0
    simp only [Nat.cast_zero, sub_zero] at hRRD0
    linarith
  have hgFF : (g : ℤ) ≤ (gFF : ℤ) := hγFF ▸ hgγ

  have hdrop : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      2 * (g : ℤ) ≤ Divisor.degree D →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ u, u ∈ riemannRochSpace D ∧ u ∉ riemannRochSpace (D - Finsupp.single x (1 : ℤ)) := by
    intro D hdegD x
    have hKD : Divisor.degree (Kω - D) < 0 := by
      rw [map_sub, hdegK]
      omega
    have hKDx : Divisor.degree (Kω - (D - Finsupp.single x (1 : ℤ))) < 0 := by
      rw [map_sub, map_sub, hdegK, hd1]
      omega
    have h1 := hRR D
    have h2 := hRR (D - Finsupp.single x (1 : ℤ))
    rw [ell_eq_zero_of_degree_neg hKD] at h1
    rw [ell_eq_zero_of_degree_neg hKDx] at h2
    simp only [Nat.cast_zero, sub_zero] at h1 h2
    rw [map_sub, hd1] at h2
    have hle : riemannRochSpace (D - Finsupp.single x (1 : ℤ)) ≤ riemannRochSpace D :=
      lSpace_mono (sub_single_le D x)
    by_contra hno
    have hsub : riemannRochSpace D ≤ riemannRochSpace (D - Finsupp.single x (1 : ℤ)) := by
      intro u hu
      by_contra hunot
      exact hno ⟨u, hu, hunot⟩
    have heq : riemannRochSpace D = riemannRochSpace (D - Finsupp.single x (1 : ℤ)) :=
      le_antisymm hsub hle
    have hcast : (ell D : ℤ) = (ell (D - Finsupp.single x (1 : ℤ)) : ℤ) := by
      have : ell D = ell (D - Finsupp.single x (1 : ℤ)) := by
        unfold ell LSpace
        rw [heq]
      exact_mod_cast this
    linarith

  have hdegE : Divisor.degree E = (embDegree N : ℤ) := by
    rw [← hEdef]
    unfold embDivisor
    rw [map_zsmul, hd1, smul_eq_mul, mul_one]
  have hembFF : (embDegree N : ℤ) = 2 * (gFF : ℤ) + 1 := by
    unfold embDegree
    rw [hgFFdef]
    push_cast
    ring
  have hEnn : (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) ≤ E := by
    refine Finsupp.le_def.mpr fun a => ?_
    rw [← hEdef]
    unfold embDivisor
    rw [Finsupp.smul_apply, Finsupp.single_apply]
    simp only [Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul]
    split <;> simp
  have hs2E : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace E := by
    rw [← hEdef]
    exact hs.2

  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr00 | hpos
    · exfalso
      subst hr00
      have hbot : riemannRochSpace E = ⊥ := by
        rw [← hs2E, Set.range_eq_empty, Submodule.span_empty]
      have h1mem : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace E :=
        lSpace_mono hEnn one_mem_lSpace_zero
      rw [hbot, Submodule.mem_bot] at h1mem
      exact one_ne_zero h1mem
    · exact hpos
  have hsne : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hsmem : ∀ i, s i ∈ riemannRochSpace E := fun i => by
    rw [← hs2E]
    exact Submodule.subset_span ⟨i, rfl⟩

  have hEbig : 2 * (g : ℤ) ≤ Divisor.degree E := by
    rw [hdegE, hembFF]
    omega
  obtain ⟨h₁, hh₁, hh₁not⟩ := hdrop E hEbig w
  have hdegEw : 2 * (g : ℤ) ≤ Divisor.degree (E - Finsupp.single w (1 : ℤ)) := by
    rw [map_sub, hdegE, hembFF, hd1]
    omega
  obtain ⟨u, hu, hunot⟩ := hdrop (E - Finsupp.single w (1 : ℤ)) hdegEw v

  obtain ⟨hh₁ne, hh₁ord⟩ := ord_pin hh₁ hh₁not
  obtain ⟨hune, huord⟩ := ord_pin hu hunot
  have huE : u ∈ riemannRochSpace E := lSpace_mono (sub_single_le E w) hu
  have hEwv : (E - Finsupp.single w (1 : ℤ)) v = E v := by
    rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hvw), sub_zero]
  rw [hEwv] at huord

  have hμle : ∀ (x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (z : modularFunctionFieldBar N),
      z ∈ riemannRochSpace E → z ≠ 0 →
      x.ord (s (pivotIndex s x hr)) ≤ x.ord z := by
    intro x z hz hzne
    refine le_ord_of_mem_span s x (fun i => pivot_min s x hr i) ?_ hzne
    rw [hs2E]
    exact hz
  have hμge : ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      -E x ≤ x.ord (s (pivotIndex s x hr)) := by
    intro x
    rcases mem_lSpace_iff_ord.mp (hsmem (pivotIndex s x hr)) with h0 | hb
    · exact absurd h0 (hsne _)
    · exact hb x
  have hμw : w.ord (s (pivotIndex s w hr)) = -E w := by
    have hle := hμle w h₁ hh₁ hh₁ne
    rw [hh₁ord] at hle
    exact le_antisymm hle (hμge w)
  have hμv : v.ord (s (pivotIndex s v hr)) = -E v := by
    have hle := hμle v u huE hune
    rw [huord] at hle
    exact le_antisymm hle (hμge v)

  have hordw_u : (1 : ℤ) - E w ≤ w.ord u := by
    rcases mem_lSpace_iff_ord.mp hu with h0 | hb
    · exact absurd h0 hune
    · have := hb w
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl] at this
      omega
  have hAw : w.evalAt (u * (s (pivotIndex s w hr))⁻¹) = 0 := by
    refine evalAt_eq_zero_of_ord_pos w (hrat w)
      (mul_ne_zero hune (inv_ne_zero (hsne _))) ?_
    rw [w.ord_mul hune (inv_ne_zero (hsne _)), w.ord_inv, hμw]
    omega
  have hAv : v.evalAt (u * (s (pivotIndex s v hr))⁻¹) ≠ 0 := by
    refine Place.evalAt_ne_zero v (hrat v)
      (mul_ne_zero hune (inv_ne_zero (hsne _))) ?_
    rw [v.ord_mul hune (inv_ne_zero (hsne _)), v.ord_inv, hμv, huord]
    ring

  have huspan : u ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by
    rw [hs2E]
    exact huE
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp huspan
  have hAvsum : v.evalAt (u * (s (pivotIndex s v hr))⁻¹) = ∑ i, c i * evalVec s v i := by
    rw [← hc]
    exact evalAt_linComb s hsne v (hrat v) hr c
  have hAwsum : w.evalAt (u * (s (pivotIndex s w hr))⁻¹) = ∑ i, c i * evalVec s w i := by
    rw [← hc]
    exact evalAt_linComb s hsne w (hrat w) hr c

  intro hchord
  have hzero : ∀ i, evalVec s v i * evalVec s w (pivotIndex s w hr)
      - evalVec s v (pivotIndex s w hr) * evalVec s w i = 0 := fun i =>
    congrFun hchord (i, pivotIndex s w hr)
  have hkw1 : evalVec s w (pivotIndex s w hr) = 1 :=
    evalVec_pivot_eq_one s w hr (hsne _)
  have hfactor : v.evalAt (u * (s (pivotIndex s v hr))⁻¹)
      = evalVec s v (pivotIndex s w hr) * ∑ i, c i * evalVec s w i := by
    rw [hAvsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := hzero i
    rw [hkw1, mul_one, sub_eq_zero] at h
    rw [h]
    ring
  rw [← hAwsum, hAw, mul_zero] at hfactor
  exact hAv hfactor

end
end S_ModularCurve_JZero_chordVec_ne_zero_of_ne
end P2MW
export P2MW.S_ModularCurve_JZero_chordVec_ne_zero_of_ne (solution)
