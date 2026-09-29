-- Prove2me | solution 1 for ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/20fdf89a-01e7-572d-abb2-6d920a32852d

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_pointHt_mul_eq_add
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_ModularCurve_constantsAreBase_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve KaehlerDifferential

noncomputable section

namespace P2MEps

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ne_zero_of_notMem {D : Divisor K F} {f : F} (hf : f ∉ riemannRochSpace D) : f ≠ 0 := by
  rintro rfl; exact hf (zero_mem _)

theorem ord_eq_of_mem_notMem {D : Divisor K F} {f : F} (w : Place K F)
    (hf : f ∈ riemannRochSpace D) (hf' : f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    w.ord f + D w = 0 := by
  classical
  have hf0 := ne_zero_of_notMem hf'
  have hge : -D w ≤ w.ord f := ((mem_riemannRochSpace_iff.mp hf) w).resolve_left hf0
  have hlt : w.ord f < -D w + 1 := by
    by_contra hge'
    push Not at hge'
    apply hf'
    rw [mem_riemannRochSpace_iff]
    intro v
    by_cases hv : v = w
    · subst hv; right
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl]; linarith
    · rcases (mem_riemannRochSpace_iff.mp hf) v with h | h
      · exact Or.inl h
      · right
        rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hv), sub_zero]; exact h
  omega

theorem exists_index_notMem_of_span_eq {ι : Type*} (x : ι → F) {D : Divisor K F}
    (hspan : Submodule.span K (Set.range x) = riemannRochSpace D) (w : Place K F)
    (h : ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    ∃ i, x i ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  by_contra hall
  push Not at hall
  obtain ⟨f, hf, hf'⟩ := h
  apply hf'
  have hle : Submodule.span K (Set.range x) ≤ riemannRochSpace (D - Finsupp.single w 1) :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
  exact hle (hspan ▸ hf)

theorem mem_of_span_eq {ι : Type*} (x : ι → F) {D : Divisor K F}
    (hspan : Submodule.span K (Set.range x) = riemannRochSpace D) (i : ι) : x i ∈ riemannRochSpace D :=
  hspan ▸ Submodule.subset_span ⟨i, rfl⟩

theorem mul_mem_rr_add {A B : Divisor K F} {f g : F} (hf : f ∈ riemannRochSpace A)
    (hg : g ∈ riemannRochSpace B) : f * g ∈ riemannRochSpace (A + B) := by
  rw [mem_riemannRochSpace_iff] at hf hg ⊢
  intro w
  rcases eq_or_ne f 0 with rfl | hf0
  · left; rw [zero_mul]
  rcases eq_or_ne g 0 with rfl | hg0
  · left; rw [mul_zero]
  right
  rw [Place.ord_mul _ hf0 hg0, Finsupp.add_apply, neg_add]
  exact add_le_add ((hf w).resolve_left hf0) ((hg w).resolve_left hg0)

theorem exists_mem_notMem_of_finrank_ne (D : Divisor K F) (w : Place K F)
    (h : Module.finrank K (riemannRochSpace D) ≠
      Module.finrank K (riemannRochSpace (D - Finsupp.single w 1))) :
    ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  classical
  have hle : riemannRochSpace (D - Finsupp.single w 1) ≤ riemannRochSpace D := by
    refine lSpace_mono (Finsupp.le_def.mpr fun v => ?_)
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hne : riemannRochSpace (D - Finsupp.single w 1) ≠ riemannRochSpace D := by
    intro heq; exact h (by rw [heq])
  obtain ⟨f, hf, hnf⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  exact ⟨f, hf, hnf⟩

theorem exists_family_span_eq (D : Divisor K F) [FiniteDimensional K (riemannRochSpace D)] :
    ∃ (c : ℕ) (t : Fin c → F), (∀ i, t i ≠ 0) ∧ Submodule.span K (Set.range t) = riemannRochSpace D ∧
      c = Module.finrank K (riemannRochSpace D) := by
  let bs := Module.finBasis K (riemannRochSpace D)
  refine ⟨_, fun i => (bs i : F), fun i => ?_, ?_, rfl⟩
  · intro h0
    apply bs.ne_zero i
    exact Subtype.ext h0
  · have hr : Set.range (fun i => (bs i : F)) = (riemannRochSpace D).subtype '' Set.range bs := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, bs.span_eq, Submodule.map_top, Submodule.range_subtype]

end Generic

section Families

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

def psz (a : ℕ) : ℕ → ℕ
  | 0 => a
  | k + 1 => psz a k * a

theorem psz_pos {a : ℕ} (ha : 0 < a) : ∀ k, 0 < psz a k
  | 0 => ha
  | k + 1 => Nat.mul_pos (psz_pos ha k) ha

def mulFam {a b : ℕ} (s : Fin a → F) (t : Fin b → F) : Fin (a * b) → F :=
  fun k => s (finProdFinEquiv.symm k).1 * t (finProdFinEquiv.symm k).2

def powFam {a : ℕ} (s : Fin a → F) : (k : ℕ) → Fin (psz a k) → F
  | 0 => s
  | k + 1 => mulFam (powFam s k) s

omit [Algebra (AlgebraicClosure ℚ) F] in
theorem mulFam_ne_zero {a b : ℕ} {s : Fin a → F} {t : Fin b → F} (hs : ∀ i, s i ≠ 0) (ht : ∀ j, t j ≠ 0) :
    ∀ k, mulFam s t k ≠ 0 := fun _ => mul_ne_zero (hs _) (ht _)

theorem powFam_ne_zero {a : ℕ} {s : Fin a → F} (hs : ∀ i, s i ≠ 0) : ∀ k idx, powFam s k idx ≠ 0
  | 0 => hs
  | k + 1 => mulFam_ne_zero (powFam_ne_zero hs k) hs

theorem mulFam_mem {a b : ℕ} {s : Fin a → F} {t : Fin b → F}
    {A B : Divisor (AlgebraicClosure ℚ) F} (hs : ∀ i, s i ∈ riemannRochSpace A) (ht : ∀ j, t j ∈ riemannRochSpace B) :
    ∀ k, mulFam s t k ∈ riemannRochSpace (A + B) := fun _ => mul_mem_rr_add (hs _) (ht _)

theorem powFam_mem {a : ℕ} {s : Fin a → F} {D : Divisor (AlgebraicClosure ℚ) F}
    (hs : ∀ i, s i ∈ riemannRochSpace D) : ∀ k idx, powFam s k idx ∈ riemannRochSpace ((k + 1) • D)
  | 0 => by simpa [powFam, psz] using hs
  | k + 1 => by
    intro idx
    have := mulFam_mem (powFam_mem hs k) hs idx
    rw [succ_nsmul]
    exact this

theorem mulFam_bpf {a b : ℕ} {s : Fin a → F} {t : Fin b → F} (hs0 : ∀ i, s i ≠ 0) (ht0 : ∀ j, t j ≠ 0)
    {A B : Divisor (AlgebraicClosure ℚ) F}
    (hs : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ i, w.ord (s i) + A w = 0)
    (ht : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ j, w.ord (t j) + B w = 0) :
    ∀ w : Place (AlgebraicClosure ℚ) F, ∃ k, w.ord (mulFam s t k) + (A + B) w = 0 := by
  intro w
  obtain ⟨i, hi⟩ := hs w
  obtain ⟨j, hj⟩ := ht w
  refine ⟨finProdFinEquiv (i, j), ?_⟩
  simp only [mulFam, Equiv.symm_apply_apply]
  rw [Place.ord_mul _ (hs0 i) (ht0 j), Finsupp.add_apply]
  linarith

theorem powFam_bpf {a : ℕ} {s : Fin a → F} (hs0 : ∀ i, s i ≠ 0) {D : Divisor (AlgebraicClosure ℚ) F}
    (hs : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ i, w.ord (s i) + D w = 0) :
    ∀ (k) (w : Place (AlgebraicClosure ℚ) F), ∃ idx, w.ord (powFam s k idx) + ((k + 1) • D) w = 0
  | 0 => by simpa [powFam, psz] using hs
  | k + 1 => by
    intro w
    have := mulFam_bpf (powFam_ne_zero hs0 k) hs0 (powFam_bpf hs0 hs k) hs w
    rw [succ_nsmul]
    exact this

theorem pointHt_powFam {a : ℕ} (ha : 0 < a) (s : Fin a → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) :
    ∀ k, pointHt (powFam s k) v = (k + 1) * pointHt s v
  | 0 => by
    have h0 : pointHt (powFam s 0) v = pointHt s v := rfl
    rw [h0]
    push_cast
    ring
  | k + 1 => by
    have h := pointHt_mul_eq_add (psz_pos ha k) ha (powFam s k) s (powFam_ne_zero hs k) hs v hv
    have h' : pointHt (powFam s (k + 1)) v = pointHt (powFam s k) v + pointHt s v := h
    rw [h', pointHt_powFam ha s hs v hv k]
    push_cast
    ring

theorem absLogHeight_nonneg' {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

theorem pointHt_nonneg {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) : 0 ≤ pointHt s v :=
  absLogHeight_nonneg' _

end Families

section Bar

variable (N : ℕ) [NeZero N]

theorem ell_eq_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1 ≤ Divisor.degree D) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI hCD : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=
    hasCanonicalDivisor_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := essFiniteType_modularFunctionFieldBar N
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  haveI hDCG : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    functionFieldRiemannRoch_modularFunctionFieldBar N
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)])
  have hdegK := degree_canonicalDivisorOf_modularFunctionFieldBar N hω
  have hgen := genus_eq_genusFF_modularFunctionFieldBar N
  have h1 := hRR hω D
  have hneg : Divisor.degree (canonicalDivisorOf hω - D) < 0 := by
    rw [map_sub, hdegK, hgen]; linarith
  have hell : ell (canonicalDivisorOf hω - D) = 0 := by
    show Module.finrank _ (LSpace _) = 0
    rw [AlgebraicCurve.lSpace_eq_bot_of_degree_neg hneg, finrank_bot]
  rw [hell, hgen] at h1
  push_cast at h1
  linarith

scoped instance finiteDimensional_lSpace_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D) := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : FiniteDimensional (AlgebraicClosure ℚ) (LSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase _ _
      (constantsAreBase_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N)
  exact finiteDimensional_lSpace D

theorem isRational_bar (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)

theorem exists_mem_notMem_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  apply exists_mem_notMem_of_finrank_ne
  have e1 := ell_eq_bar N D (by omega)
  have hdeg' : Divisor.degree (D - Finsupp.single w 1) = Divisor.degree D - 1 := by
    rw [map_sub, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N w]; push_cast; ring
  have e2 := ell_eq_bar N (D - Finsupp.single w 1) (by rw [hdeg']; omega)
  rw [hdeg'] at e2
  intro heq
  have : (ell D : ℤ) = (ell (D - Finsupp.single w 1) : ℤ) := by
    unfold ell LSpace; exact_mod_cast heq
  omega

theorem bpf_of_span_eq {ι : Type*} (x : ι → modularFunctionFieldBar N)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range x) = riemannRochSpace D)
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i, w.ord (x i) + D w = 0 := by
  intro w
  obtain ⟨i, hi⟩ := exists_index_notMem_of_span_eq x hspan w (exists_mem_notMem_bar N D hD w)
  exact ⟨i, ord_eq_of_mem_notMem w (mem_of_span_eq x hspan i) hi⟩

theorem pos_of_span_eq {a : ℕ} (x : Fin a → modularFunctionFieldBar N)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range x) = riemannRochSpace D)
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D) : 0 < a := by
  by_contra ha
  have ha0 : a = 0 := by omega
  subst ha0
  obtain ⟨f, hf, hf'⟩ := exists_mem_notMem_bar N D hD (cuspInftyBar N)
  have : f ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range x) := hspan ▸ hf
  rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
  exact ne_zero_of_notMem hf' this

theorem one_sided {a b : ℕ} (s : Fin a → modularFunctionFieldBar N) (u : Fin b → modularFunctionFieldBar N)
    (hs : ∀ i, s i ≠ 0) (hu : ∀ j, u j ≠ 0)
    (D₁ D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hd : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ Divisor.degree D₁)
    (hdeg : Divisor.degree D₁ = Divisor.degree D₂)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D₁)
    (huD : Submodule.span (AlgebraicClosure ℚ) (Set.range u) = riemannRochSpace D₂) (m : ℕ) :
    ∃ C : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ((m : ℝ) + 1) * (pointHt u v - pointHt s v) ≤ pointHt s v + C := by
  classical
  set g : ℤ := (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) with hg
  have ha : 0 < a := pos_of_span_eq N s hsD (by omega)
  have hb : 0 < b := pos_of_span_eq N u huD (by omega)

  set A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := (m + 2) • D₁ - (m + 1) • D₂ with hA
  have hdegA : Divisor.degree A = Divisor.degree D₁ := by
    rw [hA, map_sub, map_nsmul, map_nsmul, ← hdeg, nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
  have hAD : A + (m + 1) • D₂ = (m + 2) • D₁ := by rw [hA, sub_add_cancel]
  obtain ⟨c, t, ht0, htA, hc⟩ := exists_family_span_eq (K := AlgebraicClosure ℚ) A
  have hcpos : 0 < c := pos_of_span_eq N t htA (by rw [hdegA]; omega)

  have hs_bpf := bpf_of_span_eq N s hsD (by omega)
  have hu_bpf := bpf_of_span_eq N u huD (by omega)
  have ht_bpf := bpf_of_span_eq N t htA (by rw [hdegA]; omega)
  have hs_mem := mem_of_span_eq s hsD
  have hu_mem := mem_of_span_eq u huD
  have ht_mem := mem_of_span_eq t htA

  set U := powFam u m with hU
  set mixed := mulFam t U with hmixed
  set S := powFam s (m + 1) with hS
  have hU0 : ∀ idx, U idx ≠ 0 := powFam_ne_zero hu m
  have hmixed0 : ∀ k, mixed k ≠ 0 := mulFam_ne_zero ht0 hU0
  have hS0 : ∀ idx, S idx ≠ 0 := powFam_ne_zero hs (m + 1)
  have hU_mem : ∀ idx, U idx ∈ riemannRochSpace ((m + 1) • D₂) := powFam_mem hu_mem m
  have hmixed_mem : ∀ k, mixed k ∈ riemannRochSpace ((m + 2) • D₁) := by
    intro k; rw [← hAD]; exact mulFam_mem ht_mem hU_mem k
  have hS_mem : ∀ idx, S idx ∈ riemannRochSpace ((m + 2) • D₁) := by
    intro idx
    have := powFam_mem hs_mem (m + 1) idx
    exact this
  have hU_bpf := powFam_bpf hu hu_bpf m
  have hmixed_bpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ k, w.ord (mixed k) + ((m + 2) • D₁) w = 0 := by
    intro w; rw [← hAD]; exact mulFam_bpf ht0 hU0 ht_bpf hU_bpf w
  have hS_bpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ idx, w.ord (S idx) + ((m + 2) • D₁) w = 0 := powFam_bpf hs hs_bpf (m + 1)

  obtain ⟨e, wfam, hw0, hwspan, -⟩ := exists_family_span_eq (K := AlgebraicClosure ℚ) ((m + 2) • D₁)
  have hd0 : 0 ≤ Divisor.degree D₁ := by
    have : (0 : ℤ) ≤ (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := Nat.cast_nonneg _
    linarith
  have hdeg_big : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1
      ≤ Divisor.degree ((m + 2) • D₁) := by
    rw [map_nsmul, nsmul_eq_mul]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℤ) ≤ m) hd0]

  obtain ⟨C₁, hC₁⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero N
    wfam mixed hw0 hmixed0 ((m + 2) • D₁) hdeg_big hwspan hmixed_mem hmixed_bpf
  obtain ⟨C₂, hC₂⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero N
    wfam S hw0 hS0 ((m + 2) • D₁) hdeg_big hwspan hS_mem hS_bpf
  refine ⟨C₁ + C₂, fun v => ?_⟩
  have hv := isRational_bar N v

  have hmix : pointHt mixed v = pointHt t v + pointHt U v := by
    rw [hmixed]; exact pointHt_mul_eq_add hcpos (psz_pos hb m) t U ht0 hU0 v hv
  have hUeq : pointHt U v = (m + 1) * pointHt u v := by rw [hU]; exact pointHt_powFam hb u hu v hv m
  have hSeq : pointHt S v = (m + 1 + 1) * pointHt s v := by
    rw [hS]; have := pointHt_powFam ha s hs v hv (m + 1); push_cast at this; exact this
  have ht_nonneg := pointHt_nonneg t v
  have h1 := hC₁ v
  have h2 := hC₂ v
  rw [abs_le] at h1 h2
  rw [hmix, hUeq] at h1
  rw [hSeq] at h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have key : pointHt t v + (↑m + 1) * pointHt u v - (↑m + 1 + 1) * pointHt s v ≤ C₁ + C₂ := by
    linarith
  have hsplit : (↑m + 1 + 1) * pointHt s v = (↑m + 1) * pointHt s v + pointHt s v := by ring
  rw [mul_sub]
  linarith

end Bar

theorem final_ineq {n ε x y C C' : ℝ} (hn1 : 1 ≤ n) (hε : 2 ≤ ε * n) (hx : 0 ≤ x) (_hy : 0 ≤ y)
    (h1 : n * (y - x) ≤ x + C) (h2 : n * (x - y) ≤ y + C') :
    |x - y| ≤ ε * x + (|C| + |C'|) := by
  have hC : C ≤ |C| := le_abs_self C
  have hC' : C' ≤ |C'| := le_abs_self C'
  have hn0 : 0 < n := by linarith
  have hεx : 2 * x ≤ ε * n * x := by nlinarith
  have p1 : n * (2 * x) ≤ n * (ε * n * x) := mul_le_mul_of_nonneg_left hεx hn0.le
  have p2 : 0 ≤ (n - 1) * x := mul_nonneg (by linarith) hx
  have e1 : (n + 1) * x ≤ n * (n * (ε * x)) := by nlinarith [p1, p2]
  have hn2 : 1 ≤ n * n := one_le_mul_of_one_le_of_one_le hn1 hn1
  have e2 : |C| ≤ n * (n * |C|) := by
    calc |C| = |C| * 1 := by ring
      _ ≤ |C| * (n * n) := mul_le_mul_of_nonneg_left hn2 (abs_nonneg C)
      _ = n * (n * |C|) := by ring
  have e3 : n * |C'| ≤ n * (n * |C'|) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg C') hn1) hn0.le
  have e4 : x ≤ n * (ε * x) := by nlinarith [hεx]
  have e5 : |C| + |C'| ≤ n * (|C| + |C'|) := by nlinarith [abs_nonneg C, abs_nonneg C']
  rw [abs_le]
  constructor
  ·
    have h3 : n * (y - x) ≤ n * (ε * x + (|C| + |C'|)) := by
      have : x + C ≤ n * (ε * x + (|C| + |C'|)) := by nlinarith [e4, e5, abs_nonneg C']
      linarith
    have := le_of_mul_le_mul_left h3 hn0
    linarith
  · have hy' : n * y ≤ (n + 1) * x + |C| := by linarith
    have h4 : n * (n * (x - y)) ≤ n * y + n * |C'| := by nlinarith [abs_nonneg C']
    have h5 : n * (n * (x - y)) ≤ (n + 1) * x + |C| + n * |C'| := by linarith
    have h6 : (n + 1) * x + |C| + n * |C'| ≤ n * (n * (ε * x + (|C| + |C'|))) := by
      nlinarith [e1, e2, e3]
    have h7 : n * (n * (x - y)) ≤ n * (n * (ε * x + (|C| + |C'|))) := le_trans h5 h6
    have h8 := le_of_mul_le_mul_left h7 hn0
    have h9 := le_of_mul_le_mul_left h8 hn0
    linarith

end P2MEps
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq.P2MEps"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq.P2MEps"

open P2MEps in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    {a b : ℕ} (s : Fin a → ↥(ModularCurve.modularFunctionFieldBar N)) (u : Fin b → ↥(ModularCurve.modularFunctionFieldBar N))
    (hs : ∀ i, s i ≠ 0) (hu : ∀ j, u j ≠ 0)
    (D₁ D₂ : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hd : 2 * (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) + 1 ≤ D₁.degree)
    (hdeg : D₁.degree = D₂.degree)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = AlgebraicCurve.riemannRochSpace D₁)
    (huD : Submodule.span (AlgebraicClosure ℚ) (Set.range u) = AlgebraicCurve.riemannRochSpace D₂) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      |AlgebraicCurve.pointHt s v - AlgebraicCurve.pointHt u v| ≤ ε * AlgebraicCurve.pointHt s v + C := by
  intro ε hε

  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 ≤ ε * ((m : ℝ) + 1) := by
    obtain ⟨m, hm⟩ := exists_nat_ge (2 / ε)
    refine ⟨m, ?_⟩
    have : 2 / ε ≤ (m : ℝ) + 1 := by linarith
    rw [div_le_iff₀ hε] at this
    linarith
  obtain ⟨C, hC⟩ := one_sided N s u hs hu D₁ D₂ hd hdeg hsD huD m
  obtain ⟨C', hC'⟩ := one_sided N u s hu hs D₂ D₁ (hdeg ▸ hd) hdeg.symm huD hsD m
  refine ⟨|C| + |C'|, fun v => ?_⟩
  exact final_ineq (n := (m : ℝ) + 1) (by have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith) hm
    (pointHt_nonneg s v) (pointHt_nonneg u v) (hC v) (hC' v)

end S_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq
end P2MW
export P2MW.S_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq (solution)
