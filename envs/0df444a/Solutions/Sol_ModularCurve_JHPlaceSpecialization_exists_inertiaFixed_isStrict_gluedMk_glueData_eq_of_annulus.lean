-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/bcb79b53-bc8b-5070-933b-42bc2d88420a

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support
import Theorems.Thm_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_mem_hasValue
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace TorusLiftH

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_single_of_deg_eq_one (hdeg : ∀ v : Place K F, v.deg = 1) (v : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n := by
  rw [Divisor.degree_single, hdeg v, Nat.cast_one, mul_one]

theorem mk_eq_nodeUnit (S : Finset (Place K F × Place K F)) (h : F) (hh : h ≠ 0) (Dh : Divisor K F)
    (hDh : ∀ v, Dh v = v.ord h) (b : ↥S → Kˣ)
    (hval : ∀ s : ↥S, (s : Place K F × Place K F).2.HasValue h (b s))
    (hadm : ((0, Dh, 0) : GluingData K F S) ∈ GluingData.admissible S) :
    GluedPic0.mk S ⟨(0, Dh, 0), hadm⟩ = GluedPic0.nodeUnit S (fun s => Additive.ofMul (b s)) := by
  rw [GluedPic0.nodeUnit_apply, GluedPic0.mk_eq_mk_iff]
  refine ⟨1, h⁻¹, 1, fun s => (b s)⁻¹, one_ne_zero, inv_ne_zero hh, fun v => ?_, fun v => ?_,
    fun s => ⟨?_, ?_⟩, ?_⟩
  · simp
  · simp [hDh v, Place.ord_inv]
  · simpa using (s : Place K F × Place K F).1.hasValue_one
  · simpa only [Units.val_inv_eq_inv_val] using (hval s).inv (b s).ne_zero
  · funext s
    simp

end Generic

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

set_option quotPrecheck false
set_option hygiene false in
local notation "κ" => ResidueField ↥A
set_option hygiene false in
local notation "FM" => ↥(xHFunctionFieldBar M H)
set_option hygiene false in
local notation "Fb" => Fbar p M H hpM (ResidueField ↥A)
set_option hygiene false in
local notation "Φ" => qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
set_option hygiene false in
local notation "G" => arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H)

theorem degFM (V : Place (AlgebraicClosure ℚ) FM) : V.deg = 1 :=
  ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)
    (ModularCurve.translation_mem_GammaH M H) (xHFunctionField M H) rfl V

theorem degFb (hpM2 : ¬ p ^ 2 ∣ M) (w : Place κ Fb) : w.deg = 1 :=
  (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField w).mpr
    ((ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
      p M H hpM hpM2 (ResidueField ↥A)).2.2 w)

section Frame

variable {Psp : JHPlaceSpecialization p M H hpM A}
  {α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] FM}
  {hα : α.IsIntegral} {hβ : β.IsIntegral} {δ : Place κ Fb → Place κ Fb}

theorem not_isStrictSnd_of_isStrictFst (hcomm : ∀ v, Φ (δ v) = δ (Φ v))
    {W : Place (AlgebraicClosure ℚ) FM} (h : Psp.IsStrictFst α β hα hβ δ W) : ¬ Psp.IsStrictSnd α β hα hβ δ W := by
  rintro ⟨h1, h2⟩
  apply h2
  show Φ (δ (Φ (Psp.reduceSnd β hβ δ W))) = Psp.reduceSnd β hβ δ W
  rw [hcomm, ← h1]
  exact h.1

theorem not_isStrictFst_of_isStrictSnd (hcomm : ∀ v, Φ (δ v) = δ (Φ v))
    {W : Place (AlgebraicClosure ℚ) FM} (h : Psp.IsStrictSnd α β hα hβ δ W) : ¬ Psp.IsStrictFst α β hα hβ δ W :=
  fun h' => not_isStrictSnd_of_isStrictFst hcomm h' h

open Classical in

def IsGoodLift (Psp : JHPlaceSpecialization p M H hpM A)
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] FM)
    (hα : α.IsIntegral) (hβ : β.IsIntegral) (δ : Place κ Fb → Place κ Fb)
    (D : Divisor (AlgebraicClosure ℚ) FM) (E₁ E₂ : Divisor κ Fb) : Prop :=
  Psp.IsGoodDiv α β hα hβ δ D ∧ Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) = E₁ ∧
    Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) = E₂ ∧
    Divisor.degree D = Divisor.degree E₁ + Divisor.degree E₂ ∧
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • D = D) ∧
    ∀ V ∈ D.support, ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • V = V

open Classical in
theorem isGoodLift_zero : IsGoodLift Psp α β hα hβ δ 0 0 0 := by
  refine ⟨fun V hV => absurd hV (by simp), ?_, ?_, ?_, fun σ _ => smul_zero _, fun V hV => absurd hV (by simp)⟩
  · unfold JHPlaceSpecialization.fstDiv
    rw [Finsupp.filter_zero, Finsupp.mapDomain_zero]
  · unfold JHPlaceSpecialization.sndDiv
    rw [Finsupp.filter_zero, Finsupp.mapDomain_zero]
  · simp only [map_zero, add_zero]

open Classical in
theorem fstDiv_add (D D' : Divisor (AlgebraicClosure ℚ) FM) :
    Psp.fstDiv α β hα hβ δ (D + D') = Psp.fstDiv α β hα hβ δ D + Psp.fstDiv α β hα hβ δ D' := by
  unfold JHPlaceSpecialization.fstDiv
  exact Finsupp.filter_add

open Classical in
theorem sndDiv_add (D D' : Divisor (AlgebraicClosure ℚ) FM) :
    Psp.sndDiv α β hα hβ δ (D + D') = Psp.sndDiv α β hα hβ δ D + Psp.sndDiv α β hα hβ δ D' := by
  unfold JHPlaceSpecialization.sndDiv
  exact Finsupp.filter_add

theorem IsGoodLift.add {D D' : Divisor (AlgebraicClosure ℚ) FM} {E₁ E₂ E₁' E₂' : Divisor κ Fb}
    (h : IsGoodLift Psp α β hα hβ δ D E₁ E₂) (h' : IsGoodLift Psp α β hα hβ δ D' E₁' E₂') :
    IsGoodLift Psp α β hα hβ δ (D + D') (E₁ + E₁') (E₂ + E₂') := by
  classical
  obtain ⟨hg, h1, h2, hd, hi, hf⟩ := h
  obtain ⟨hg', h1', h2', hd', hi', hf'⟩ := h'
  refine ⟨fun W hW => ?_, ?_, ?_, ?_, fun σ hσ => ?_, fun V hV => ?_⟩
  · rcases Finset.mem_union.mp (Finsupp.support_add hW) with hW | hW
    · exact hg W hW
    · exact hg' W hW
  · rw [fstDiv_add, Finsupp.mapDomain_add, h1, h1']
  · rw [sndDiv_add, Finsupp.mapDomain_add, h2, h2']
  · rw [map_add, map_add, map_add, hd, hd']
    abel
  · rw [smul_add, hi σ hσ, hi' σ hσ]
  · rcases Finset.mem_union.mp (Finsupp.support_add hV) with hV | hV
    · exact hf V hV
    · exact hf' V hV

open Classical in

theorem isGoodLift_single_fst (hpM2 : ¬ p ^ 2 ∣ M) (hcomm : ∀ v, Φ (δ v) = δ (Φ v))
    {V : Place (AlgebraicClosure ℚ) FM} (hV : Psp.IsStrictFst α β hα hβ δ V)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • V = V) (n : ℤ) :
    IsGoodLift Psp α β hα hβ δ (Finsupp.single V n) (Finsupp.single (Psp.reduceFst α hα V) n) 0 := by
  refine ⟨fun W hW => ?_, ?_, ?_, ?_, fun σ hσ => ?_, fun V' hV' => ?_⟩
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hW)]
    exact Or.inl hV
  · unfold JHPlaceSpecialization.fstDiv
    rw [Finsupp.filter_single_of_pos _ hV, Finsupp.mapDomain_single]
  · unfold JHPlaceSpecialization.sndDiv
    rw [Finsupp.filter_single_of_neg _ (not_isStrictSnd_of_isStrictFst hcomm hV), Finsupp.mapDomain_zero]
  · rw [degree_single_of_deg_eq_one degFM, degree_single_of_deg_eq_one (degFb hpM2), map_zero, add_zero]
  · rw [SemilinearAut.smul_single, hfix σ hσ]
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hV')]
    exact hfix

open Classical in

theorem isGoodLift_single_snd (hpM2 : ¬ p ^ 2 ∣ M) (hcomm : ∀ v, Φ (δ v) = δ (Φ v))
    {V : Place (AlgebraicClosure ℚ) FM} (hV : Psp.IsStrictSnd α β hα hβ δ V)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • V = V) (n : ℤ) :
    IsGoodLift Psp α β hα hβ δ (Finsupp.single V n) 0 (Finsupp.single (Psp.reduceSnd β hβ δ V) n) := by
  refine ⟨fun W hW => ?_, ?_, ?_, ?_, fun σ hσ => ?_, fun V' hV' => ?_⟩
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hW)]
    exact Or.inr hV
  · unfold JHPlaceSpecialization.fstDiv
    rw [Finsupp.filter_single_of_neg _ (not_isStrictFst_of_isStrictSnd hcomm hV), Finsupp.mapDomain_zero]
  · unfold JHPlaceSpecialization.sndDiv
    rw [Finsupp.filter_single_of_pos _ hV, Finsupp.mapDomain_single]
  · rw [degree_single_of_deg_eq_one degFM, degree_single_of_deg_eq_one (degFb hpM2), map_zero, zero_add]
  · rw [SemilinearAut.smul_single, hfix σ hσ]
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hV')]
    exact hfix

section Lifts

variable (hpM2 : ¬ p ^ 2 ∣ M) (hcomm : ∀ v, Φ (δ v) = δ (Φ v))
  (B : Finset (Place κ Fb))
  (hB : ∀ v : Place κ Fb, v ∉ B →
    (∃ W : Place (AlgebraicClosure ℚ) FM, Psp.IsStrictFst α β hα hβ δ W ∧ Psp.reduceFst α hα W = v ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • W = W) ∧
    (∃ W : Place (AlgebraicClosure ℚ) FM, Psp.IsStrictSnd α β hα hβ δ W ∧ Psp.reduceSnd β hβ δ W = v ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • W = W))
include hpM2 hcomm hB

theorem exists_isGoodLift_sum_fst (c : Place κ Fb → ℤ) :
    ∀ s : Finset (Place κ Fb), (∀ v ∈ s, v ∉ B) →
      ∃ D : Divisor (AlgebraicClosure ℚ) FM, IsGoodLift Psp α β hα hβ δ D (∑ v ∈ s, Finsupp.single v (c v)) 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, by rw [Finset.sum_empty]; exact isGoodLift_zero⟩
  | insert a s ha ih =>
    intro hs
    obtain ⟨D, hD⟩ := ih (fun v hv => hs v (Finset.mem_insert_of_mem hv))
    obtain ⟨V, hV, hred, hfix⟩ := (hB a (hs a (Finset.mem_insert_self a s))).1
    refine ⟨Finsupp.single V (c a) + D, ?_⟩
    rw [Finset.sum_insert ha, ← add_zero (0 : Divisor κ Fb)]
    have h1 := isGoodLift_single_fst hpM2 hcomm hV hfix (c a)
    rw [hred] at h1
    exact h1.add hD

theorem exists_isGoodLift_sum_snd (c : Place κ Fb → ℤ) :
    ∀ s : Finset (Place κ Fb), (∀ v ∈ s, v ∉ B) →
      ∃ D : Divisor (AlgebraicClosure ℚ) FM, IsGoodLift Psp α β hα hβ δ D 0 (∑ v ∈ s, Finsupp.single v (c v)) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, by rw [Finset.sum_empty]; exact isGoodLift_zero⟩
  | insert a s ha ih =>
    intro hs
    obtain ⟨D, hD⟩ := ih (fun v hv => hs v (Finset.mem_insert_of_mem hv))
    obtain ⟨V, hV, hred, hfix⟩ := (hB a (hs a (Finset.mem_insert_self a s))).2
    refine ⟨Finsupp.single V (c a) + D, ?_⟩
    rw [Finset.sum_insert ha, ← add_zero (0 : Divisor κ Fb)]
    have h1 := isGoodLift_single_snd hpM2 hcomm hV hfix (c a)
    rw [hred] at h1
    exact h1.add hD

theorem exists_isGoodLift (E₁ E₂ : Divisor κ Fb)
    (hE₁ : ∀ v ∈ E₁.support, v ∉ B) (hE₂ : ∀ v ∈ E₂.support, v ∉ B) :
    ∃ D : Divisor (AlgebraicClosure ℚ) FM, IsGoodLift Psp α β hα hβ δ D E₁ E₂ := by
  obtain ⟨D₁, hD₁⟩ := exists_isGoodLift_sum_fst hpM2 hcomm B hB E₁ E₁.support hE₁
  obtain ⟨D₂, hD₂⟩ := exists_isGoodLift_sum_snd hpM2 hcomm B hB E₂ E₂.support hE₂
  have h1 : (∑ v ∈ E₁.support, Finsupp.single v (E₁ v)) = E₁ := Finsupp.sum_single E₁
  have h2 : (∑ v ∈ E₂.support, Finsupp.single v (E₂ v)) = E₂ := Finsupp.sum_single E₂
  rw [h1] at hD₁
  rw [h2] at hD₂
  refine ⟨D₁ + D₂, ?_⟩
  have h := hD₁.add hD₂
  rwa [add_zero, zero_add] at h

end Lifts

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem torus_lift (hpM2 : ¬ p ^ 2 ∣ M) (hcomm : ∀ v, Φ (δ v) = δ (Φ v))
    (SS : Finset (Place κ Fb × Place κ Fb))
    (hSS2 : ∀ s ∈ SS, ∀ s' ∈ SS, s.2 = s'.2 → s = s') (hSSne : SS.Nonempty)
    (hsurj : ∀ w : Place κ Fb, Function.Surjective (algebraMap κ w.ResidueField))
    [HasPrincipalDivisors κ Fb]
    (B : Finset (Place κ Fb))
    (hB : ∀ v : Place κ Fb, v ∉ B →
      (∃ W : Place (AlgebraicClosure ℚ) FM, Psp.IsStrictFst α β hα hβ δ W ∧ Psp.reduceFst α hα W = v ∧
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • W = W) ∧
      (∃ W : Place (AlgebraicClosure ℚ) FM, Psp.IsStrictSnd α β hα hβ δ W ∧ Psp.reduceSnd β hβ δ W = v ∧
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • W = W))
    (hBS : ∀ s ∈ SS, s.1 ∈ B ∧ s.2 ∈ B)
    (g : GluedPic0 κ Fb SS) :
    ∃ Dt : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM)),
      (∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) FM).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • V = V) ∧ (Psp.IsStrictFst α β hα hβ δ V ∨ Psp.IsStrictSnd α β hα hβ δ V)) ∧
      ∃ hadm : Psp.glueData α β hα hβ δ SS (Dt : Divisor (AlgebraicClosure ℚ) FM) ∈ GluingData.admissible SS,
        GluedPic0.mk SS ⟨Psp.glueData α β hα hβ δ SS (Dt : Divisor (AlgebraicClosure ℚ) FM), hadm⟩ = g := by
  classical

  obtain ⟨E₁, hE₁c, hE₁B⟩ := AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support (GluedPic0.toPic0Pair SS g).1 B
  obtain ⟨E₂, hE₂c, hE₂B⟩ := AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support (GluedPic0.toPic0Pair SS g).2 B
  obtain ⟨Dab, hab_good, hab_fst, hab_snd, hab_deg, hab_inv, hab_fix⟩ :=
    exists_isGoodLift hpM2 hcomm B hB (E₁ : Divisor κ Fb) E₂ hE₁B hE₂B
  have hadm_ab : (((E₁ : Divisor κ Fb), (E₂ : Divisor κ Fb), 0) : GluingData κ Fb SS) ∈ GluingData.admissible SS := by
    refine ⟨E₁.2, E₂.2, fun s hs => ⟨?_, ?_⟩⟩
    · by_contra h
      exact hE₁B _ (Finsupp.mem_support_iff.mpr h) (hBS s hs).1
    · by_contra h
      exact hE₂B _ (Finsupp.mem_support_iff.mpr h) (hBS s hs).2
  have hglue_ab : Psp.glueData α β hα hβ δ SS Dab = (((E₁ : Divisor κ Fb), (E₂ : Divisor κ Fb), 0)) :=
    Prod.ext hab_fst (Prod.ext hab_snd rfl)
  have hadmDab : Psp.glueData α β hα hβ δ SS Dab ∈ GluingData.admissible SS := by rw [hglue_ab]; exact hadm_ab
  have hab : GluedPic0.toPic0Pair SS (GluedPic0.mk SS ⟨_, hadmDab⟩) = GluedPic0.toPic0Pair SS g := by
    rw [show (⟨Psp.glueData α β hα hβ δ SS Dab, hadmDab⟩ : ↥(GluingData.admissible SS)) = ⟨_, hadm_ab⟩ from Subtype.ext hglue_ab,
      GluedPic0.toPic0Pair_mk]
    exact Prod.ext hE₁c hE₂c

  have hker : g - GluedPic0.mk SS ⟨_, hadmDab⟩ ∈ (GluedPic0.toPic0Pair SS).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hab, sub_self]
  rw [AlgebraicCurve.GluedPic0.ker_toPic0Pair_eq_range_nodeUnit SS (fun s => ⟨hsurj _, hsurj _⟩)] at hker
  obtain ⟨w, hw⟩ := hker

  let b : ↥SS → κˣ := fun s => Additive.toMul (w s)
  let c : Place κ Fb → κˣ := fun e => if h : ∃ s : ↥SS, (s : Place κ Fb × Place κ Fb).2 = e then b h.choose else 1
  have hcs : ∀ s : ↥SS, c (s : Place κ Fb × Place κ Fb).2 = b s := by
    intro s
    have hex : ∃ s' : ↥SS, (s' : Place κ Fb × Place κ Fb).2 = (s : Place κ Fb × Place κ Fb).2 := ⟨s, rfl⟩
    have hs' : hex.choose = s := Subtype.ext (hSS2 _ hex.choose.2 _ s.2 hex.choose_spec)
    simp only [c, dif_pos hex, hs']
  obtain ⟨h, hval⟩ := AlgebraicCurve.Place.exists_forall_mem_hasValue B c
  have hh0 : h ≠ 0 := by
    obtain ⟨s, hs⟩ := hSSne
    exact (hval _ (hBS s hs).2).ne_zero (c _).ne_zero
  obtain ⟨Dh, hDh, hDh0⟩ := HasPrincipalDivisors.exists_divisor (K := κ) h hh0
  have hordB : ∀ v ∈ B, v.ord h = 0 := fun v hv => (hval v hv).ord_eq_zero (c v).ne_zero
  have hDhB : ∀ v ∈ Dh.support, v ∉ B := fun v hv hvB =>
    (Finsupp.mem_support_iff.mp hv) (by rw [hDh v, hordB v hvB])
  obtain ⟨Dt, ht_good, ht_fst, ht_snd, ht_deg, ht_inv, ht_fix⟩ :=
    exists_isGoodLift hpM2 hcomm B hB 0 Dh (fun v hv => absurd hv (by simp)) hDhB
  have hadm_t : ((0, Dh, 0) : GluingData κ Fb SS) ∈ GluingData.admissible SS :=
    ⟨zero_mem _, Divisor.mem_degZero.mpr hDh0, fun s hs =>
      ⟨rfl, by show Dh s.2 = 0; rw [hDh, hordB _ (hBS s hs).2]⟩⟩
  have hglue_t : Psp.glueData α β hα hβ δ SS Dt = (0, Dh, 0) :=
    Prod.ext ht_fst (Prod.ext ht_snd rfl)
  have hadmDt : Psp.glueData α β hα hβ δ SS Dt ∈ GluingData.admissible SS := by rw [hglue_t]; exact hadm_t
  have ht : GluedPic0.mk SS ⟨_, hadmDt⟩ = GluedPic0.nodeUnit SS w := by
    rw [show (⟨Psp.glueData α β hα hβ δ SS Dt, hadmDt⟩ : ↥(GluingData.admissible SS)) = ⟨(0, Dh, 0), hadm_t⟩ from Subtype.ext hglue_t]
    have hwb : w = fun s => Additive.ofMul (b s) := by
      funext s; simp only [b, ofMul_toMul]
    rw [hwb]
    exact mk_eq_nodeUnit SS h hh0 Dh hDh b (fun s => by rw [← hcs s]; exact hval _ (hBS s s.2).2) hadm_t

  have hdeg0 : Dab + Dt ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM) := by
    rw [Divisor.mem_degZero, map_add, hab_deg, ht_deg, Divisor.mem_degZero.mp E₁.2, Divisor.mem_degZero.mp E₂.2, map_zero, hDh0]
    simp
  have hglue : Psp.glueData α β hα hβ δ SS (Dab + Dt) = Psp.glueData α β hα hβ δ SS Dab + Psp.glueData α β hα hβ δ SS Dt := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ (Dab + Dt)) = _
      rw [fstDiv_add, Finsupp.mapDomain_add]; rfl
    · show Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ (Dab + Dt)) = _
      rw [sndDiv_add, Finsupp.mapDomain_add]; rfl
    · show (0 : ↥SS → Additive κˣ) = 0 + 0
      rw [add_zero]
  have hadm : Psp.glueData α β hα hβ δ SS (Dab + Dt) ∈ GluingData.admissible SS := by
    rw [hglue]; exact AddSubgroup.add_mem _ hadmDab hadmDt
  refine ⟨⟨Dab + Dt, hdeg0⟩, ?_, hadm, ?_⟩
  · intro V hV
    rcases Finset.mem_union.mp (Finsupp.support_add hV) with hV | hV
    · exact ⟨hab_fix V hV, hab_good V hV⟩
    · exact ⟨ht_fix V hV, ht_good V hV⟩
  · rw [show (⟨Psp.glueData α β hα hβ δ SS (Dab + Dt), hadm⟩ : ↥(GluingData.admissible SS)) = ⟨_, hadmDab⟩ + ⟨_, hadmDt⟩
        from Subtype.ext hglue, map_add, ht, hw]
    abel

end Frame

end TorusLiftH

end

open TorusLiftH in
open Classical in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (g : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS) :
    ∃ Dt : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧
        (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V)) ∧
      ∃ hadm : Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (Dt : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS,
        GluedPic0.mk SS ⟨Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (Dt : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = g := by

  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hk] at this
    rw [← this]; ring
  have hcomm : ∀ v, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ v) =
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v) := by
    intro v
    rw [hδ v, hδ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)]
    exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
      (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) v

  have hfb := ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2 (ResidueField ↥A)
  haveI := hfb.1
  have hSS2 : ∀ s ∈ SS, ∀ s' ∈ SS, s.2 = s'.2 → s = s' := by
    intro s hs s' hs' h2
    have hn := (mem_ssNodePairsQExp_iff _).mp ((hSS _).mp hs)
    have hn' := (mem_ssNodePairsQExp_iff _).mp ((hSS _).mp hs')
    exact Prod.ext (by rw [hn.2, hn'.2, h2]) h2
  have hSSne : SS.Nonempty := by
    obtain ⟨y, hy⟩ := ModularCurve.nonempty_ssPlacesQExp (M / p) (ΓN p M H hpM)
      (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM)) (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM))
      p hpN (ResidueField ↥A)
    exact ⟨_, (hSS _).mpr (frob_mk_mem_ssNodePairsQExp hy)⟩

  obtain ⟨Bad₀, hBad₀⟩ := ModularCurve.JHPlaceSpecialization.exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift
    p M H hpM hpM2 hHp A hA θ α (θ.toAlgHom.comp α) hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hreg hnv hα_coe hβ_coe hθgal rfl hLFst hLSnd hUnit
  refine torus_lift hpM2 hcomm SS hSS2 hSSne hfb.2.2 (Bad₀ ∪ (SS.image Prod.fst ∪ SS.image Prod.snd))
    (fun v hv => hBad₀ v (fun h => hv (Finset.mem_union_left _ h)))
    (fun s hs => ⟨Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs)),
      Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs))⟩) g

end S_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus (solution)
