-- Prove2me | solution 1 for ModularCurve.FullLevel.existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/388b00d7-90f7-5dfe-88be-e181327195bf

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_three
import Theorems.Thm_ModularCurve_isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_three
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace RAM0

section Phi

variable (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] (N : ℕ) [NeZero N]

theorem qExpand_prime_jqModC : qExpand K q (jqModC K) = jqModC K ^ q :=
  frobenius_identity_geom_unconditional K

theorem qExpand_prime_jqNModC : qExpand K q (jqNModC K N) = jqNModC K N ^ q := by
  unfold jqNModC
  rw [qExpand_qExpand, qExpand_congr (mul_comm q N), ← qExpand_qExpand, qExpand_prime_jqModC, map_pow]

theorem qExpand_prime_mem {g : LaurentSeries K} (hg : g ∈ modularFunctionFieldC K N) :
    qExpand K q g ∈ modularFunctionFieldC K N := by
  have hj : jqModC K ∈ modularFunctionFieldC K N := jqModC_mem K N
  have hjN : jqNModC K N ∈ modularFunctionFieldC K N := jqNModC_mem K N
  have h : modularFunctionFieldC K N ≤ (modularFunctionFieldC K N).comap (qExpandAlgC K q) := by
    conv_lhs => unfold modularFunctionFieldC
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    change qExpandAlgC K q x ∈ modularFunctionFieldC K N
    rw [qExpandAlgC_apply]
    rcases Set.mem_insert_iff.mp hx with h1 | h2
    · rw [h1, qExpand_prime_jqModC]
      exact pow_mem hj _
    · rw [Set.mem_singleton_iff.mp h2, qExpand_prime_jqNModC]
      exact pow_mem hjN _
  exact h hg

noncomputable def Phi : ↥(modularFunctionFieldC K N) →ₐ[K] ↥(modularFunctionFieldC K N) where
  toFun g := ⟨qExpand K q (g : LaurentSeries K), qExpand_prime_mem K q N g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by
    show qExpand K q (algebraMap K (LaurentSeries K) r) = algebraMap K (LaurentSeries K) r
    exact (qExpandAlgC K q).commutes r)

@[scoped simp] theorem coe_Phi (g : ↥(modularFunctionFieldC K N)) :
    ((Phi K q N g : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = qExpand K q (g : LaurentSeries K) := rfl

theorem coe_Phi_Phi (g : ↥(modularFunctionFieldC K N)) :
    ((Phi K q N (Phi K q N g) : ↥(modularFunctionFieldC K N)) : LaurentSeries K) =
      qExpand K (q ^ 2) (g : LaurentSeries K) := by
  rw [coe_Phi, coe_Phi, qExpand_qExpand, qExpand_congr (pow_two q).symm]

theorem isFrobeniusEndo_Phi (hperf : ∀ c : K, ∃ d : K, d ^ q = c) : IsFrobeniusEndo q (Phi K q N) := by
  haveI : CharP (LaurentSeries K) q := charP_laurentSeries (ℓ := q) K
  have hC : ∀ c : K, qExpand K q (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c :=
    fun c => (qExpandAlgC K q).commutes c
  refine ⟨fun x => ?_, fun y => ?_⟩
  ·
    have key : ∀ z : LaurentSeries K, z ∈ modularFunctionFieldC K N →
        ∃ w : LaurentSeries K, w ∈ modularFunctionFieldC K N ∧ qExpand K q w = z ^ q := by
      intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem y hy =>
        rcases hy with rfl | rfl
        · exact ⟨jqModC K, jqModC_mem K N, qExpand_prime_jqModC K q⟩
        · exact ⟨jqNModC K N, jqNModC_mem K N, qExpand_prime_jqNModC K q N⟩
      | algebraMap c =>
        refine ⟨algebraMap K (LaurentSeries K) (c ^ q), (modularFunctionFieldC K N).algebraMap_mem _, ?_⟩
        rw [hC, map_pow]
      | add y z _ _ hy hz =>
        obtain ⟨w₁, hw₁, e₁⟩ := hy
        obtain ⟨w₂, hw₂, e₂⟩ := hz
        exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, e₁, e₂, add_pow_char]⟩
      | inv y _ hy =>
        obtain ⟨w, hw, e⟩ := hy
        exact ⟨w⁻¹, inv_mem hw, by rw [map_inv₀, e, inv_pow]⟩
      | mul y z _ _ hy hz =>
        obtain ⟨w₁, hw₁, e₁⟩ := hy
        obtain ⟨w₂, hw₂, e₂⟩ := hz
        exact ⟨w₁ * w₂, mul_mem hw₁ hw₂, by rw [map_mul, e₁, e₂, mul_pow]⟩
    obtain ⟨w, hw, e⟩ := key x x.2
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [coe_Phi]
    push_cast
    exact e
  ·
    have key : ∀ z : LaurentSeries K, z ∈ modularFunctionFieldC K N →
        ∃ w : LaurentSeries K, w ∈ modularFunctionFieldC K N ∧ qExpand K q z = w ^ q := by
      intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem y hy =>
        rcases hy with rfl | rfl
        · exact ⟨jqModC K, jqModC_mem K N, qExpand_prime_jqModC K q⟩
        · exact ⟨jqNModC K N, jqNModC_mem K N, qExpand_prime_jqNModC K q N⟩
      | algebraMap c =>
        obtain ⟨d, hd⟩ := hperf c
        refine ⟨algebraMap K (LaurentSeries K) d, (modularFunctionFieldC K N).algebraMap_mem _, ?_⟩
        rw [hC, ← map_pow, hd]
      | add y z _ _ hy hz =>
        obtain ⟨w₁, hw₁, e₁⟩ := hy
        obtain ⟨w₂, hw₂, e₂⟩ := hz
        exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, e₁, e₂, add_pow_char]⟩
      | inv y _ hy =>
        obtain ⟨w, hw, e⟩ := hy
        exact ⟨w⁻¹, inv_mem hw, by rw [map_inv₀, e, inv_pow]⟩
      | mul y z _ _ hy hz =>
        obtain ⟨w₁, hw₁, e₁⟩ := hy
        obtain ⟨w₂, hw₂, e₂⟩ := hz
        exact ⟨w₁ * w₂, mul_mem hw₁ hw₂, by rw [map_mul, e₁, e₂, mul_pow]⟩
    obtain ⟨w, hw, e⟩ := key y y.2
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [coe_Phi]
    push_cast
    exact e

end Phi

theorem mem_restrictAlong_iff' {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring := by
  rw [show (w.restrictAlong φ hφ).toValuationSubring = w.toValuationSubring.comap φ.toRingHom from rfl,
    ValuationSubring.mem_comap]
  exact Iff.rfl

end RAM0
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_three.RAM0"

open ModularCurve.FullLevel IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    (hint : RingHom.IsIntegral (IntermediateField.inclusion hle).toRingHom)
    (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))
    (hs : s ∈ ssPlaces q M' (ResidueField A)) :
    ∃! w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      ∀ (g : ↥(modularFunctionFieldC (ResidueField A) M'))
        (g' : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
        (g' : LaurentSeries (ResidueField A)) = qExpand (ResidueField A) (q ^ 2) (g : LaurentSeries (ResidueField A)) →
        (g ∈ s.toValuationSubring ↔ g' ∈ w.toValuationSubring) := by
  classical
  haveI hchar : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  haveI hac : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hperf : ∀ c : ResidueField ↥A, ∃ d : ResidueField ↥A, d ^ q = c :=
    fun c => IsAlgClosed.exists_pow_nat_eq c (Fact.out : q.Prime).pos
  have hFE : IsFrobeniusEndo q (RAM0.Phi (ResidueField ↥A) q M') :=
    RAM0.isFrobeniusEndo_Phi (ResidueField ↥A) q M' hperf
  have hΦint : (RAM0.Phi (ResidueField ↥A) q M').toRingHom.IsIntegral := hFE.isIntegral hq0
  haveI hcharE : CharP ↥(modularFunctionFieldC (ResidueField ↥A) M') q :=
    charP_modularFunctionFieldC (ResidueField ↥A) M'
  have hrat : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'), v.IsRational :=
    fun v => (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed (ResidueField ↥A) M' v)

  have step : ∀ (v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'))
      (g : ↥(modularFunctionFieldC (ResidueField ↥A) M')),
      g ∈ v.toValuationSubring ↔ RAM0.Phi (ResidueField ↥A) q M' g ∈ (hFE.extendPlace v).toValuationSubring := by
    intro v g
    have h := RAM0.mem_restrictAlong_iff' (RAM0.Phi (ResidueField ↥A) q M') hΦint (hFE.extendPlace v) g
    rw [hFE.restrictAlong_extendPlace hΦint v] at h
    exact h

  set s' : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    hFE.extendPlace (hFE.extendPlace s) with hs'def
  have hs' : ∀ g : ↥(modularFunctionFieldC (ResidueField ↥A) M'),
      g ∈ s.toValuationSubring ↔
        RAM0.Phi (ResidueField ↥A) q M' (RAM0.Phi (ResidueField ↥A) q M' g) ∈ s'.toValuationSubring :=
    fun g => (step s g).trans (step (hFE.extendPlace s) _)
  have hs'ss : s' ∈ ssPlaces q M' (ResidueField ↥A) := by
    rw [mem_ssPlaces_iff] at hs ⊢
    exact isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand q M' (ResidueField ↥A) 2
      ((RAM0.Phi (ResidueField ↥A) q M').comp (RAM0.Phi (ResidueField ↥A) q M')).toRingHom
      (fun g => RAM0.coe_Phi_Phi (ResidueField ↥A) q M' g) s s' hs' (hrat s') hs
  obtain ⟨w, hw, huniq⟩ :=
    existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_three q hq3 M' hqM' A hA hle hint s' hs'ss
  refine ⟨w, ?_, ?_⟩
  · intro g g' hg'
    have hg'eq : g' = IntermediateField.inclusion hle
        (RAM0.Phi (ResidueField ↥A) q M' (RAM0.Phi (ResidueField ↥A) q M' g)) := by
      apply Subtype.ext
      rw [IntermediateField.coe_inclusion, hg', RAM0.coe_Phi_Phi]
    rw [hg'eq, ← RAM0.mem_restrictAlong_iff' (IntermediateField.inclusion hle) hint w, hw]
    exact hs' g
  · intro w₂ hw₂
    apply huniq
    apply hFE.restrictAlong_injective hq0 hΦint
    apply hFE.restrictAlong_injective hq0 hΦint
    rw [hs'def, hFE.restrictAlong_extendPlace hΦint, hFE.restrictAlong_extendPlace hΦint]
    refine Place.ext (SetLike.ext fun g => ?_)
    rw [RAM0.mem_restrictAlong_iff', RAM0.mem_restrictAlong_iff', RAM0.mem_restrictAlong_iff']
    exact (hw₂ g _ (by rw [IntermediateField.coe_inclusion, RAM0.coe_Phi_Phi])).symm

end S_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_three (solution)
