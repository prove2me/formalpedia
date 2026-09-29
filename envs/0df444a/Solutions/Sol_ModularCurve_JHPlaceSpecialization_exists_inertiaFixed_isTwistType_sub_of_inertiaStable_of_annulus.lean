-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/576662f1-effb-5b91-84e5-5494e0f76f86

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType
import Theorems.Thm_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace TwistH

theorem sum_laplace_Ico (f : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Ico 1 n, (f (d - 1) - 2 * f d + f (d + 1)) = f 0 - f 1 - f (n - 1) + f n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega), ih hm]
      obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

theorem tent_sum (n : ℕ) (δ : ℚ) (h0 : 0 ≤ δ) (hn : δ ≤ n) :
    ∑ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) = 1 := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hlt : δ < ⌊δ⌋₊ + 1 := Nat.lt_floor_add_one δ
  have hmn : ⌊δ⌋₊ ≤ n := Nat.floor_le_of_le (by exact_mod_cast hn)

  have hterm : ∀ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) =
      (if d = ⌊δ⌋₊ then 1 - (δ - ⌊δ⌋₊) else 0) + (if d = ⌊δ⌋₊ + 1 then δ - ⌊δ⌋₊ else 0) := by
    intro d _
    by_cases h1 : d = ⌊δ⌋₊
    · subst h1
      have h2 : ¬ (⌊δ⌋₊ = ⌊δ⌋₊ + 1) := by omega
      rw [if_pos rfl, if_neg h2, add_zero, abs_of_nonneg (by linarith)]
      exact max_eq_right (by linarith)
    · rw [if_neg h1, zero_add]
      by_cases h2 : d = ⌊δ⌋₊ + 1
      · subst h2
        rw [if_pos rfl, abs_of_nonpos (by push_cast; linarith)]
        push_cast
        rw [max_eq_right (by linarith)]
        ring
      · rw [if_neg h2]
        apply max_eq_left

        rcases Nat.lt_or_gt_of_ne h1 with h | h
        ·
          have : (d : ℚ) + 1 ≤ ⌊δ⌋₊ := by exact_mod_cast h
          rw [abs_of_nonneg (by linarith)]
          linarith
        ·
          have : (⌊δ⌋₊ : ℚ) + 2 ≤ d := by exact_mod_cast (show ⌊δ⌋₊ + 2 ≤ d by omega)
          rw [abs_of_nonpos (by linarith)]
          linarith
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' , Finset.sum_ite_eq']
  have hm : ⌊δ⌋₊ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos hm]
  by_cases hm1 : ⌊δ⌋₊ + 1 ∈ Finset.range (n + 1)
  · rw [if_pos hm1]; ring
  · rw [if_neg hm1, add_zero]

    have h3 : ⌊δ⌋₊ = n := by rw [Finset.mem_range] at hm1; omega
    have h4 : δ = n := le_antisymm hn (by rw [← h3]; exact hfl)
    rw [h4]; simp

theorem tent_one (d : ℕ) : max 0 (1 - |(1 : ℚ) - (d : ℚ)|) = if d = 1 then 1 else 0 := by
  by_cases h : d = 1
  · subst h; simp
  · rw [if_neg h]
    apply max_eq_left
    rcases Nat.lt_or_gt_of_ne h with h0 | h2
    · have : d = 0 := by omega
      subst this; simp
    · have : (2 : ℚ) ≤ d := by exact_mod_cast h2
      rw [abs_of_nonpos (by linarith)]; linarith

section Degree

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum_support (h1 : ∀ V : Place K F, V.deg = 1) (D : Divisor K F) :
    Divisor.degree D = ∑ V ∈ D.support, D V := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [Divisor.degree_single, h1]
  simp

theorem degree_filter (h1 : ∀ V : Place K F, V.deg = 1) (D : Divisor K F) (q : Place K F → Prop) [DecidablePred q] :
    Divisor.degree (D.filter q) = ∑ V ∈ D.support with q V, D V := by
  classical
  rw [degree_eq_sum_support h1, Finsupp.support_filter]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finsupp.filter_apply_pos]
  exact (Finset.mem_filter.mp hV).2

end Degree

section JH

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
variable (Psp : JHPlaceSpecialization p M H hpM A)
  (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))

theorem not_isStrictSnd_of_isStrictFst {V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)}
    (h1 : Psp.IsStrictFst α β hα hβ δ V) : ¬ Psp.IsStrictSnd α β hα hβ δ V := fun h2 =>
  h1.2 (show qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
      (Psp.reduceFst α hα V))) = Psp.reduceFst α hα V by rw [h1.1, ← h2.1])

open Classical in

theorem degree_decomp₀ (h1 : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.deg = 1) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Divisor.degree D = Divisor.degree (Psp.fstDiv α β hα hβ δ D) + Divisor.degree (Psp.sndDiv α β hα hβ δ D) +
      ∑ V ∈ D.support with (¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V), D V := by
  have hF : Divisor.degree (Psp.fstDiv α β hα hβ δ D) = ∑ V ∈ D.support with Psp.IsStrictFst α β hα hβ δ V, D V := by
    unfold JHPlaceSpecialization.fstDiv; convert degree_filter h1 D (Psp.IsStrictFst α β hα hβ δ)
  have hS : Divisor.degree (Psp.sndDiv α β hα hβ δ D) = ∑ V ∈ D.support with Psp.IsStrictSnd α β hα hβ δ V, D V := by
    unfold JHPlaceSpecialization.sndDiv; convert degree_filter h1 D (Psp.IsStrictSnd α β hα hβ δ)
  rw [hF, hS, degree_eq_sum_support h1]
  have step1 := (Finset.sum_filter_add_sum_filter_not D.support (Psp.IsStrictFst α β hα hβ δ) (fun V => D V)).symm
  have step2 := (Finset.sum_filter_add_sum_filter_not (D.support.filter fun V => ¬ Psp.IsStrictFst α β hα hβ δ V)
    (Psp.IsStrictSnd α β hα hβ δ) (fun V => D V)).symm
  rw [step1, step2, Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  refine Finset.sum_congr (Finset.filter_congr fun V _ => ?_) fun _ _ => rfl
  exact ⟨fun h => h.2, fun h => ⟨fun h' => not_isStrictSnd_of_isStrictFst Psp α β hα hβ δ h' h, h⟩⟩

open Classical in

theorem degree_decomp (h1 : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.deg = 1)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom →
      ¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V)
    (hdisj : ∀ (s s' : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom → V ∈ (An s').dom → s = s')
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hgood : ∀ V ∈ D.support, Psp.IsStrictFst α β hα hβ δ V ∨ Psp.IsStrictSnd α β hα hβ δ V ∨ ∃ s : ↥SS, V ∈ (An s).dom) :
    Divisor.degree D = Divisor.degree (Psp.fstDiv α β hα hβ δ D) + Divisor.degree (Psp.sndDiv α β hα hβ δ D) +
      ∑ s : ↥SS, ∑ V ∈ D.support with V ∈ (An s).dom, D V := by
  rw [degree_decomp₀ Psp α β hα hβ δ h1 D]
  congr 1
  have key : ∀ V ∈ D.support,
      (if (¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V) then D V else 0)
        = ∑ s : ↥SS, if V ∈ (An s).dom then D V else 0 := by
    intro V hV
    by_cases h : ∃ s : ↥SS, V ∈ (An s).dom
    · obtain ⟨s₀, hs₀⟩ := h
      rw [if_pos (hAn s₀ V hs₀), Finset.sum_eq_single s₀ (fun s _ hne => if_neg (fun hs => hne (hdisj s s₀ V hs hs₀)))
        (fun h => absurd (Finset.mem_univ _) h), if_pos hs₀]
    · have hstrict : ¬ (¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V) := by
        intro hn
        apply h
        rcases hgood V hV with h' | h' | h'
        · exact absurd h' hn.1
        · exact absurd h' hn.2
        · exact h'
      rw [if_neg hstrict]
      symm
      exact Finset.sum_eq_zero fun s _ => if_neg (fun hs => h ⟨s, hs⟩)
  rw [Finset.sum_filter, Finset.sum_congr rfl key, Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => (Finset.sum_filter _ _).symm

variable (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
  (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
  (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)

open Classical in

noncomputable def tentFn (s : ↥SS) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : ℚ :=
  if V ∈ (An s).dom then max 0 (1 - |pos s V - d|) else 0

noncomputable def circleHom (s : ↥SS) (d : ℕ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →+ ℚ :=
  Finsupp.liftAddHom fun V => (AddMonoidHom.mulRight (tentFn SS An pos s d V)).comp (Int.castAddHom ℚ)

open Classical in
theorem circleDeg_eq_circleHom (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) (d : ℕ) :
    JHPlaceSpecialization.twistCircleDeg SS An pos D s d = circleHom SS An pos s d D := by
  unfold JHPlaceSpecialization.twistCircleDeg circleHom
  rw [Finsupp.liftAddHom_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun V _ => ?_
  unfold tentFn
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mulRight, Function.comp_apply, Int.coe_castAddHom]
  split_ifs <;> simp

theorem circleHom_single (s : ↥SS) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (n : ℤ) :
    circleHom SS An pos s d (Finsupp.single V n) = n * tentFn SS An pos s d V := by
  unfold circleHom
  rw [Finsupp.liftAddHom_apply_single]
  simp

open Classical in
theorem tentFn_of_not_mem (s : ↥SS) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (h : V ∉ (An s).dom) :
    tentFn SS An pos s d V = 0 := by
  unfold tentFn
  rw [if_neg h]

open Classical in

theorem tentFn_of_strict (s : ↥SS) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hAn : V ∈ (An s).dom → ¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V)
    (h : Psp.IsStrictFst α β hα hβ δ V ∨ Psp.IsStrictSnd α β hα hβ δ V) :
    tentFn SS An pos s d V = 0 := by
  apply tentFn_of_not_mem
  intro hmem
  rcases h with h | h
  · exact (hAn hmem).1 h
  · exact (hAn hmem).2 h

end JH

end TwistH

open Classical in
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

    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
    (hpos : JHPlaceSpecialization.AnnulusPositionLaw SS e An pos)
    (hposσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V)
    (hposD : ∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d)
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    :
    ∃ Dfix : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (∀ V ∈ (Dfix : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧
        (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) ∧
      Psp.IsTwistType α (θ.toAlgHom.comp α) hα hβ δ SS e An pos ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - Dfix) := by
  classical

  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  haveI hCObar : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  have hdeg1all : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.deg = 1 := fun V =>
    IsCurveOver.deg_eq_one_of_isAlgClosed V
  have hint : ∀ (w : ↥SS) (d : ℕ), (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w d).den = 1 :=
    ModularCurve.JHPlaceSpecialization.den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn An hAn pos hpos hposσ X hXst

  have hdomns : ∀ (w : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An w).dom → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V :=
    fun w V hV => ⟨((hAn w).1 V |>.mp hV).2.1, ((hAn w).1 V |>.mp hV).2.2⟩
  have hdomr : ∀ (w : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An w).dom → Psp.reduceFst α hα V = w.1.1 := fun w V hV => ((hAn w).1 V |>.mp hV).1
  have hX1 : ∀ s ∈ SS, ∀ s' ∈ SS, s.1 = s'.1 → s = s' := by
    intro s hs s' hs' h
    have h2 := (mem_ssNodePairsQExp_iff _).mp ((hSS s).mp hs)
    have h2' := (mem_ssNodePairsQExp_iff _).mp ((hSS s').mp hs')
    have hinj := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM)).1
    exact Prod.ext h (hinj (h2.2.symm.trans (h.trans h2'.2)))
  have hdisj : ∀ (s s' : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom → V ∈ (An s').dom → s = s' := fun s s' V h h' =>
    Subtype.ext (hX1 s.1 s.2 s'.1 s'.2 ((hdomr s V h).symm.trans (hdomr s' V h')))
  have hX2 : ∀ s ∈ SS, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = s.1 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V := by
    intro s hs V hV
    have h2 := (mem_ssNodePairsQExp_iff _).mp ((hSS s).mp hs)
    have hfix2 := hFix s.2 h2.1
    have hFixed1 : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ s.1 := by
      rw [h2.2]; exact hfix2.2
    have hinj := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM)).1
    refine ⟨fun hst => hst.2 (hV ▸ hFixed1), fun hst => hst.2 ?_⟩
    have h3 : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V) =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p s.2 := hst.1.symm.trans (hV.trans h2.2)
    rw [hinj h3]
    exact hfix2.1

  have hgood_of : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s : ↥SS, V ∈ (An s).dom := by
    intro V h
    rcases h with h | h | ⟨s, hs, hV⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨⟨s, hs⟩, ((hAn ⟨s, hs⟩).1 V).mpr ⟨hV, hX2 s hs V hV⟩⟩)
  have hXgood : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s : ↥SS, V ∈ (An s).dom := fun V hV => hgood_of V (hXsupp V hV)

  have hposb : ∀ (w : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An w).dom → 0 < pos w V ∧ pos w V < e w := fun w V hV => ⟨(hpos w V hV).1, (hpos w V hV).2.1⟩
  have hw1 : ∀ w : ↥SS, 1 ≤ e w := fun w => he w

  obtain ⟨r, hr⟩ : ∃ r : ↥SS → ℕ → ℤ, r = fun w d => (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w d).num := ⟨_, rfl⟩
  have hrq : ∀ (w : ↥SS) (d : ℕ), (r w d : ℚ) = JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w d := fun w d => by
    rw [hr]; exact Rat.coe_int_num_of_den_eq_one (hint w d)
  have hGG := ModularCurve.ChainDirichlet.exists_depthOne_correction_dirichlet e hw1 r
  obtain ⟨ν, c, hν1, hc0, hcn, hclap⟩ := hGG
  have hν0 : ∀ w : ↥SS, ¬ 2 ≤ e w → ν w = 0 := fun w h => hν1 w (by have := hw1 w; omega)

  let a : JHPlaceSpecialization.TwistVec ↥SS := ⟨0, 0, c⟩
  have hchain : ∀ (w : ↥SS) (d : ℕ), JHPlaceSpecialization.twistChainVal SS e a w d = c w d := by
    intro w d
    unfold JHPlaceSpecialization.twistChainVal
    by_cases hd0 : d = 0
    · rw [if_pos hd0, hd0, hc0]
    · rw [if_neg hd0]
      by_cases hdw : e w ≤ d
      · rw [if_pos hdw, hcn w d hdw]
      · rw [if_neg hdw]

  have hFAM := ModularCurve.JHPlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
    p M H hpM hpM2 hHp A hA θ α (θ.toAlgHom.comp α) hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hreg hnv hα_coe hβ_coe hθgal rfl hLFst hLSnd hUnit ∅ 1 1
  obtain ⟨Q₁, Q₂, hQ₁s, hQ₂s, -, -, -, -, hQ₁fix, hQ₂fix⟩ := hFAM
  have hV₁s : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (Q₁ 0) := hQ₁s 0
  have hV₂s : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (Q₂ 0) := hQ₂s 0
  have hnF2 : ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (Q₂ 0) := fun h => TwistH.not_isStrictSnd_of_isStrictFst Psp α (θ.toAlgHom.comp α) hα hβ δ h hV₂s
  have hnS1 : ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (Q₁ 0) := TwistH.not_isStrictSnd_of_isStrictFst Psp α (θ.toAlgHom.comp α) hα hβ δ hV₁s

  have hVex : ∀ w : ↥SS, ∃ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), 2 ≤ e w → V ∈ (An w).dom ∧ (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos w V = 1 := by
    intro w
    by_cases h2 : 2 ≤ e w
    · obtain ⟨V, hVd, hVf, hV1⟩ := hposD w 1 one_pos (by omega)
      exact ⟨V, fun _ => ⟨hVd, hVf, by exact_mod_cast hV1⟩⟩
    · exact ⟨Q₁ 0, fun h => absurd h h2⟩
  choose Vf hVf using hVex

  obtain ⟨S, hS⟩ : ∃ S : ℤ, S = ∑ w : ↥SS, ν w := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = -(Divisor.degree (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))) - S - ∑ w : ↥SS, JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w := ⟨_, rfl⟩
  obtain ⟨Dann, hDann⟩ : ∃ Dann : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Dann = ∑ w : ↥SS, ν w • Finsupp.single (Vf w) (1 : ℤ) := ⟨_, rfl⟩
  obtain ⟨Dfix, hDfix⟩ : ∃ Dfix : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Dfix = Dann + m • Finsupp.single (Q₂ 0) (1 : ℤ) - (m + S) • Finsupp.single (Q₁ 0) (1 : ℤ) := ⟨_, rfl⟩
  have hDann_apply : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Dann V = ∑ w : ↥SS, ν w * (Finsupp.single (Vf w) (1 : ℤ) V) := by
    intro V
    rw [hDann, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul]
  have hVf_ns : ∀ w : ↥SS, ν w ≠ 0 → Vf w ∈ (An w).dom ∧ (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (Vf w) = (Vf w)) ∧ pos w (Vf w) = 1 := by
    intro w hν
    have h2 : 2 ≤ e w := by
      by_contra h2
      exact hν (hν0 w h2)
    exact hVf w h2
  have hDann_strict : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → Dann V = 0 := by
    intro V hV
    rw [hDann_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases hν : ν w = 0
    · rw [hν, zero_mul]
    · rw [Finsupp.single_apply, if_neg, mul_zero]
      rintro rfl
      obtain ⟨hd, -, -⟩ := hVf_ns w hν
      rcases hV with h | h
      · exact (hdomns w _ hd).1 h
      · exact (hdomns w _ hd).2 h
  have hDann_supp : ∀ V ∈ Dann.support, ∃ w : ↥SS, ν w ≠ 0 ∧ V = Vf w := by
    intro V hV
    rw [Finsupp.mem_support_iff, hDann_apply] at hV
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
    refine ⟨w, fun h => hw (by rw [h, zero_mul]), ?_⟩
    by_contra hne
    apply hw
    rw [Finsupp.single_apply, if_neg (fun h => hne h.symm), mul_zero]
  have hsingle_supp : ∀ (V W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (n : ℤ), V ∈ (n • Finsupp.single W (1 : ℤ)).support → V = W := by
    intro V W n h
    have := Finsupp.support_smul h
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at this
    exact this

  have hDfixsupp' : ∀ V ∈ Dfix.support, (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ w : ↥SS, ν w ≠ 0 ∧ V = Vf w) := by
    intro V hV
    rw [hDfix] at hV
    rcases Finset.mem_union.mp (Finsupp.support_sub hV) with h | h
    · rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
      · obtain ⟨w, hν, rfl⟩ := hDann_supp V h
        exact ⟨(hVf_ns w hν).2.1, Or.inr (Or.inr ⟨w, hν, rfl⟩)⟩
      · have hV2 := hsingle_supp V _ _ h
        subst hV2
        exact ⟨hQ₂fix 0, Or.inr (Or.inl hV₂s)⟩
    · have hV1 := hsingle_supp V _ _ h
      subst hV1
      exact ⟨hQ₁fix 0, Or.inl hV₁s⟩
  have hDfixsupp : ∀ V ∈ Dfix.support, (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) := by
    intro V hV
    obtain ⟨hfix, h⟩ := hDfixsupp' V hV
    refine ⟨hfix, ?_⟩
    rcases h with h | h | ⟨w, hν, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨w.1, w.2, hdomr w _ (hVf_ns w hν).1⟩)

  have hdeg1 : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Divisor.degree (Finsupp.single V (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = 1 := fun V => by
    rw [Divisor.degree_single, hdeg1all]; simp
  have hdegDann : Divisor.degree Dann = S := by
    rw [hDann, map_sum, hS]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_zsmul, hdeg1, smul_eq_mul, mul_one]
  have hdegDfix : Divisor.degree Dfix = 0 := by
    rw [hDfix, map_sub, map_add, map_zsmul, map_zsmul, hdegDann, hdeg1, hdeg1]
    ring
  refine ⟨⟨Dfix, Divisor.mem_degZero.mpr hdegDfix⟩, hDfixsupp, a, ?_⟩

  show Psp.IsTwistOf α (θ.toAlgHom.comp α) hα hβ δ SS e An pos a ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - Dfix)
  obtain ⟨D, hD⟩ : ∃ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), D = (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - Dfix := ⟨_, rfl⟩
  rw [← hD]
  have htent : ∀ (w : ↥SS) (d : ℕ) (w' : ↥SS), ν w' * TwistH.tentFn SS An pos w d (Vf w') =
      if w' = w then (if d = 1 then (ν w' : ℚ) else 0) else 0 := by
    intro w d w'
    by_cases hν : ν w' = 0
    · rw [hν]; simp
    · obtain ⟨hd', -, hdep⟩ := hVf_ns w' hν
      unfold TwistH.tentFn
      by_cases hww : w' = w
      · subst hww
        rw [if_pos hd', hdep, TwistH.tent_one, if_pos rfl]
        split_ifs <;> simp
      · rw [if_neg, if_neg hww, mul_zero]
        intro hd
        exact hww (hdisj w' w _ hd' hd)
  have hcDfix : ∀ (w : ↥SS) (d : ℕ), JHPlaceSpecialization.twistCircleDeg SS An pos Dfix w d = if d = 1 then (ν w : ℚ) else 0 := by
    intro w d
    rw [TwistH.circleDeg_eq_circleHom, hDfix, map_sub, map_add, map_zsmul, map_zsmul, hDann, map_sum,
      TwistH.circleHom_single, TwistH.circleHom_single,
      TwistH.tentFn_of_strict Psp α (θ.toAlgHom.comp α) hα hβ δ SS An pos _ _ _ (hdomns w _) (Or.inl hV₁s),
      TwistH.tentFn_of_strict Psp α (θ.toAlgHom.comp α) hα hβ δ SS An pos _ _ _ (hdomns w _) (Or.inr hV₂s), mul_zero, smul_zero, smul_zero, add_zero, sub_zero]
    rw [Finset.sum_congr rfl (fun w' _ => by rw [map_zsmul, TwistH.circleHom_single, zsmul_eq_mul, Int.cast_one, one_mul]),
      Finset.sum_congr rfl (fun w' _ => htent w d w'), Finset.sum_ite_eq' Finset.univ w, if_pos (Finset.mem_univ _)]
  have hcD : ∀ (w : ↥SS) (d : ℕ), JHPlaceSpecialization.twistCircleDeg SS An pos D w d = JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w d - if d = 1 then (ν w : ℚ) else 0 := by
    intro w d
    rw [hD, TwistH.circleDeg_eq_circleHom, map_sub, ← TwistH.circleDeg_eq_circleHom, ← TwistH.circleDeg_eq_circleHom, hcDfix]
  have hcD0 : ∀ w : ↥SS, JHPlaceSpecialization.twistCircleDeg SS An pos D w 0 = JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w 0 := fun w => by
    rw [hcD]; simp
  have hcDn : ∀ w : ↥SS, JHPlaceSpecialization.twistCircleDeg SS An pos D w (e w) = JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w (e w) := fun w => by
    rw [hcD]
    by_cases h2 : 2 ≤ e w
    · rw [if_neg (by omega), sub_zero]
    · rw [hν0 w h2]; simp
  have hintD : ∀ (w : ↥SS) (d : ℕ), (JHPlaceSpecialization.twistCircleDeg SS An pos D w d).den = 1 := by
    intro w d
    rw [hcD, ← hrq]
    split_ifs
    · exact_mod_cast (show ((r w d - ν w : ℤ) : ℚ).den = 1 from Rat.den_intCast _)
    · rw [sub_zero]; exact Rat.den_intCast _

  have hshF : ∀ w : ↥SS, JHPlaceSpecialization.twistEndShareFst SS An pos D w = r w 0 := fun w => by
    unfold JHPlaceSpecialization.twistEndShareFst
    rw [if_pos (hintD w 0), hcD0, hr]
  have hshS : ∀ w : ↥SS, JHPlaceSpecialization.twistEndShareSnd SS e An pos D w = r w (e w) := fun w => by
    unfold JHPlaceSpecialization.twistEndShareSnd
    rw [if_pos (hintD w _), hcDn, hr]
  have hshFX : ∀ w : ↥SS, JHPlaceSpecialization.twistEndShareFst SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w = r w 0 := fun w => by
    unfold JHPlaceSpecialization.twistEndShareFst
    rw [if_pos (hint w 0), hr]
  have hoF : ∀ w : ↥SS, JHPlaceSpecialization.twistEndOrderFst SS e An pos a D w = JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w := fun w => by
    unfold JHPlaceSpecialization.twistEndOrderFst
    rw [hshF, hshFX]

  have hfst_apply : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D V = Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V + (m + S) * (Finsupp.single (Q₁ 0) (1 : ℤ) V) := by
    intro V
    unfold JHPlaceSpecialization.fstDiv
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hV : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V
    · rw [if_pos hV, if_pos hV, hD, Finsupp.sub_apply, hDfix, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.smul_apply, hDann_strict V (Or.inl hV), smul_eq_mul, smul_eq_mul]
      have h2 : Finsupp.single (Q₂ 0) (1 : ℤ) V = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hnF2 hV
      rw [h2]
      ring
    · rw [if_neg hV, if_neg hV]
      have h1 : Finsupp.single (Q₁ 0) (1 : ℤ) V = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hV hV₁s
      rw [h1]
      ring
  have hsnd_apply : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D V = Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V - m * (Finsupp.single (Q₂ 0) (1 : ℤ) V) := by
    intro V
    unfold JHPlaceSpecialization.sndDiv
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hV : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V
    · rw [if_pos hV, if_pos hV, hD, Finsupp.sub_apply, hDfix, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.smul_apply, hDann_strict V (Or.inr hV), smul_eq_mul, smul_eq_mul]
      have h2 : Finsupp.single (Q₁ 0) (1 : ℤ) V = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hnS1 hV
      rw [h2]
      ring
    · rw [if_neg hV, if_neg hV]
      have h1 : Finsupp.single (Q₂ 0) (1 : ℤ) V = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hV hV₂s
      rw [h1]
      ring
  have hfst : Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D = Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) + (m + S) • Finsupp.single (Q₁ 0) 1 := by
    ext V
    rw [hfst_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hsnd : Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D = Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - m • Finsupp.single (Q₂ 0) 1 := by
    ext V
    rw [hsnd_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  have hdegF : Divisor.degree (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) = Divisor.degree (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) + (m + S) := by
    rw [hfst, map_add, map_zsmul, hdeg1, smul_eq_mul, mul_one]
  have hdegS : Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D) = Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) - m := by
    rw [hsnd, map_sub, map_zsmul, hdeg1, smul_eq_mul, mul_one]

  have E1 : Divisor.degree (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) = -∑ w : ↥SS, JHPlaceSpecialization.twistEndOrderFst SS e An pos a D w := by
    rw [hdegF, Finset.sum_congr rfl (fun w _ => hoF w), hm]
    ring

  have E3 : ∀ (w : ↥SS) (d : ℕ), 1 ≤ d → d + 1 ≤ e w →
      JHPlaceSpecialization.twistCircleDeg SS An pos D w d = -((JHPlaceSpecialization.twistChainVal SS e a w (d - 1) - 2 * JHPlaceSpecialization.twistChainVal SS e a w d +
        JHPlaceSpecialization.twistChainVal SS e a w (d + 1) : ℤ) : ℚ) := by
    intro w d hd1 hd2
    have hcl := hclap w d hd1 hd2
    rw [hchain, hchain, hchain, hcl, hcD w d, ← hrq w d]
    split_ifs <;> push_cast <;> ring

  have hDpos : ∀ V ∈ D.support, ∀ w : ↥SS, V ∈ (An w).dom → 0 < pos w V ∧ pos w V < e w := fun V _ w hV => hposb w V hV
  have hann : ∀ w : ↥SS,
      ∑ V ∈ D.support with V ∈ (An w).dom, (D V : ℚ) =
        JHPlaceSpecialization.twistEndOrderFst SS e An pos a D w + JHPlaceSpecialization.twistEndOrderSnd SS e An pos a D w := by
    intro w
    have hn1 : 1 ≤ e w := hw1 w
    have h1 : ∑ V ∈ D.support with V ∈ (An w).dom, (D V : ℚ) = ∑ d ∈ Finset.range (e w + 1), JHPlaceSpecialization.twistCircleDeg SS An pos D w d := by
      unfold JHPlaceSpecialization.twistCircleDeg
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun V hV => ?_
      obtain ⟨hVs, hVw⟩ := Finset.mem_filter.mp hV
      obtain ⟨h0, hlt⟩ := hDpos V hVs w hVw
      rw [← Finset.mul_sum, TwistH.tent_sum _ _ h0.le (by exact_mod_cast hlt.le), mul_one]
    have h2 : ∑ d ∈ Finset.range (e w + 1), JHPlaceSpecialization.twistCircleDeg SS An pos D w d =
        JHPlaceSpecialization.twistCircleDeg SS An pos D w 0 + ∑ d ∈ Finset.Ico 1 (e w), JHPlaceSpecialization.twistCircleDeg SS An pos D w d + JHPlaceSpecialization.twistCircleDeg SS An pos D w (e w) := by
      rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn1]
    have h3 : JHPlaceSpecialization.twistCircleDeg SS An pos D w 0 = JHPlaceSpecialization.twistEndShareFst SS An pos D w := by
      rw [hshF, hrq, hcD0]
    have h4 : JHPlaceSpecialization.twistCircleDeg SS An pos D w (e w) = JHPlaceSpecialization.twistEndShareSnd SS e An pos D w := by
      rw [hshS, hrq, hcDn]
    have h5 : ∑ d ∈ Finset.Ico 1 (e w), JHPlaceSpecialization.twistCircleDeg SS An pos D w d =
        ((JHPlaceSpecialization.twistChainVal SS e a w 1 - JHPlaceSpecialization.twistChainVal SS e a w 0) +
          (JHPlaceSpecialization.twistChainVal SS e a w (e w - 1) - JHPlaceSpecialization.twistChainVal SS e a w (e w)) : ℤ) := by
      rw [Finset.sum_congr rfl (fun d hd => E3 w d (Finset.mem_Ico.mp hd).1 (by have := (Finset.mem_Ico.mp hd).2; omega))]
      rw [Finset.sum_neg_distrib]
      have hL := congrArg (fun z : ℤ => (z : ℚ)) (TwistH.sum_laplace_Ico (fun d => JHPlaceSpecialization.twistChainVal SS e a w d) (e w) hn1)
      push_cast at hL ⊢
      rw [hL]
      ring
    rw [h1, h2, h3, h4, h5]
    unfold JHPlaceSpecialization.twistEndOrderFst JHPlaceSpecialization.twistEndOrderSnd
    push_cast; ring

  have hdeg0 : Divisor.degree D = 0 := by
    rw [hD, map_sub, hdegDfix, sub_zero]
    exact Divisor.mem_degZero.mp X.2
  have hgoodD : ∀ V ∈ D.support, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s : ↥SS, V ∈ (An s).dom := by
    intro V hV
    rw [hD] at hV
    rcases Finset.mem_union.mp (Finsupp.support_sub hV) with h | h
    · exact hXgood V h
    · exact hgood_of V (hDfixsupp V h).2
  have hdec := TwistH.degree_decomp Psp α (θ.toAlgHom.comp α) hα hβ δ hdeg1all SS An (fun s V hV => hdomns s V hV) hdisj D hgoodD
  have E2 : Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D) = -∑ w : ↥SS, JHPlaceSpecialization.twistEndOrderSnd SS e An pos a D w := by
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hdec
    simp only [hdeg0] at hc
    push_cast at hc
    rw [Finset.sum_congr rfl (fun w _ => hann w), Finset.sum_add_distrib] at hc
    have hE1 := congrArg (fun z : ℤ => (z : ℚ)) E1
    push_cast at hE1
    have : (Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D) : ℚ) = -∑ w : ↥SS, (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a D w : ℚ) := by linarith
    exact_mod_cast this
  exact ⟨E1, E2, E3⟩

end S_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isTwistType_sub_of_inertiaStable_of_annulus (solution)
