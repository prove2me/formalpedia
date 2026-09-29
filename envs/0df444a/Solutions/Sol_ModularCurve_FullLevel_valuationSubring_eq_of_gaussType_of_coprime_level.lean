-- Prove2me | solution 1 for ModularCurve.FullLevel.valuationSubring_eq_of_gaussType_of_coprime_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e96a164d-6a53-59ba-9da2-958c2555488e

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le
import Theorems.Thm_ValuationSubring_mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_valuationSubring_eq_of_gaussType_of_coprime_level
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace GaussExistsUnram_node13

open AlgebraicCurve

theorem transcendental_of_coe_eq_jqModC (K : Type) [Field K] (E : IntermediateField K (LaurentSeries K))
    (x : ↥E) (hx : (x : LaurentSeries K) = jqModC K) : Transcendental K x := by
  have h := ModularCurve.transcendental_jqModC K
  rw [← hx] at h
  exact (transcendental_algebraMap_iff (R := K) (S := ↥E) (A := LaurentSeries K) Subtype.val_injective).mp h

theorem inv_mem_of_isUnit {F : Type} [Field F] (S : ValuationSubring F) (t : ↥S) (ht : IsUnit t) :
    ((t : F))⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := ht
  have hmul : (t : F) * (((u⁻¹ : (↥S)ˣ) : ↥S) : F) = 1 := by
    have h := congrArg (fun z : ↥S => (z : F)) u.mul_inv
    simp only [hu] at h
    exact h
  by_cases ht0 : (t : F) = 0
  · rw [ht0, zero_mul] at hmul; exact absurd hmul zero_ne_one
  rw [inv_eq_of_mul_eq_one_right hmul]
  exact Subtype.mem _

theorem gaussType_and_unramified
    {L : Type} [Field L] (A₀ : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F] [Algebra ↥A₀ F] [IsScalarTower ↥A₀ L F]
    {Fbar : Type} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A₀) Fbar]
    (R : RegularProlongation A₀ F Fbar)
    (π₀ : ↥A₀) (hunif : IsLocalRing.maximalIdeal ↥A₀ = Ideal.span {π₀}) (hπ0 : π₀ ≠ 0)
    (j : F) (hj : j ∈ R.integers) (hjt : Transcendental (IsLocalRing.ResidueField ↥A₀) (R.residue ⟨j, hj⟩)) :
    (∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ R.integers) ∧
    algebraMap ↥A₀ F π₀ ∈ R.integers.nonunits ∧
    (∀ P : Polynomial ↥A₀, ¬ (Polynomial.C π₀ ∣ P) →
      Polynomial.aeval j P ∈ R.integers ∧ (Polynomial.aeval j P)⁻¹ ∈ R.integers) ∧
    (∀ f : F, f ∈ R.integers.nonunits → f * (algebraMap ↥A₀ F π₀)⁻¹ ∈ R.integers) := by
  classical
  have halg : ∀ r : ↥A₀, algebraMap ↥A₀ F r = algebraMap L F (r : L) := fun r =>
    IsScalarTower.algebraMap_apply ↥A₀ L F r

  let ψ : ↥A₀ →+* ↥R.integers :=
    { toFun := fun a => ⟨algebraMap L F (a : L), (R.algebraMap_mem_iff (a : L)).mpr a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hψ : ∀ a : ↥A₀, ((ψ a : ↥R.integers) : F) = algebraMap ↥A₀ F a := fun a => (halg a).symm
  have hψres : R.residue.comp ψ = (algebraMap (IsLocalRing.ResidueField ↥A₀) Fbar).comp (IsLocalRing.residue ↥A₀) :=
    RingHom.ext fun a => R.residue_algebraMap a
  have hRV : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ R.integers := fun r => by rw [← hψ]; exact (ψ r).2

  have hπ𝔪 : π₀ ∈ IsLocalRing.maximalIdeal ↥A₀ := by rw [hunif]; exact Ideal.mem_span_singleton_self _
  have hϖV : algebraMap ↥A₀ F π₀ ∈ R.integers.nonunits := by
    rw [← hψ]
    apply ValuationSubring.coe_mem_nonunits_iff.mpr
    rw [← R.ker_residue, RingHom.mem_ker, show R.residue (ψ π₀) = (R.residue.comp ψ) π₀ from rfl, hψres,
      RingHom.comp_apply, (IsLocalRing.residue_eq_zero_iff _).mpr hπ𝔪, map_zero]

  have hjV : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C π₀ ∣ P) →
      Polynomial.aeval j P ∈ R.integers ∧ (Polynomial.aeval j P)⁻¹ ∈ R.integers := by
    intro P hP

    have hPbar : P.map (IsLocalRing.residue ↥A₀) ≠ 0 := by
      intro h0
      apply hP
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi : (P.map (IsLocalRing.residue ↥A₀)).coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
      rw [Polynomial.coeff_map, IsLocalRing.residue_eq_zero_iff, hunif] at hi
      exact Ideal.mem_span_singleton.mp hi

    let u : ↥R.integers := P.eval₂ ψ ⟨j, hj⟩
    have hu : (u : F) = Polynomial.aeval j P := by
      show R.integers.subtype (P.eval₂ ψ ⟨j, hj⟩) = _
      rw [Polynomial.hom_eval₂, Polynomial.aeval_def]
      congr 1
      exact RingHom.ext fun a => hψ a
    have hures : R.residue u = Polynomial.aeval (R.residue ⟨j, hj⟩) (P.map (IsLocalRing.residue ↥A₀)) := by
      show R.residue (P.eval₂ ψ ⟨j, hj⟩) = _
      rw [Polynomial.hom_eval₂, hψres, ← Polynomial.eval₂_map, Polynomial.aeval_def]
    have hune : R.residue u ≠ 0 := by
      rw [hures]
      intro h0
      exact hjt ⟨P.map (IsLocalRing.residue ↥A₀), hPbar, h0⟩
    refine ⟨hu ▸ u.2, ?_⟩
    rw [← hu]
    exact inv_mem_of_isUnit R.integers u (R.isUnit_of_residue_ne_zero hune)

  have hunr : ∀ f : F, f ∈ R.integers.nonunits → f * (algebraMap ↥A₀ F π₀)⁻¹ ∈ R.integers := by
    intro f hf
    by_cases hf0 : f = 0
    · rw [hf0, zero_mul]; exact R.integers.zero_mem
    have hfV : f ∈ R.integers := (R.integers.valuation_le_one_iff f).mp
      (le_of_lt ((R.integers.mem_nonunits_iff).mp hf))
    obtain ⟨c, hc, hcres⟩ := R.exists_smul_mem f hf0
    have hcu : IsUnit (⟨c • f, hc⟩ : ↥R.integers) := R.isUnit_of_residue_ne_zero hcres
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hcres
      have : (⟨(0 : L) • f, hc⟩ : ↥R.integers) = 0 := Subtype.ext (by simp)
      rw [this, map_zero]
    have hcf : c • f = algebraMap L F c * f := Algebra.smul_def c f

    have hginv : (algebraMap L F c)⁻¹ = f * (c • f)⁻¹ := by
      rw [hcf, mul_inv, mul_comm ((algebraMap L F c)⁻¹), ← mul_assoc, mul_inv_cancel₀ hf0, one_mul]
    have hval1 : R.integers.valuation (c • f) = 1 := by
      have := R.integers.valuation_unit hcu.unit
      simpa using this
    have hgnu : algebraMap L F c⁻¹ ∈ R.integers.nonunits := by
      rw [map_inv₀, hginv, R.integers.mem_nonunits_iff, map_mul, map_inv₀, hval1, inv_one, mul_one]
      exact (R.integers.mem_nonunits_iff).mp hf
    have hgV : algebraMap L F c⁻¹ ∈ R.integers :=
      (R.integers.valuation_le_one_iff _).mp (le_of_lt ((R.integers.mem_nonunits_iff).mp hgnu))
    have hcA : c⁻¹ ∈ A₀ := (R.algebraMap_mem_iff _).mp hgV

    have hc𝔪 : (⟨c⁻¹, hcA⟩ : ↥A₀) ∈ IsLocalRing.maximalIdeal ↥A₀ := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      apply (algebraMap (IsLocalRing.ResidueField ↥A₀) Fbar).injective
      rw [map_zero, ← RingHom.comp_apply, ← hψres, RingHom.comp_apply, ← RingHom.mem_ker, R.ker_residue,
        ← ValuationSubring.coe_mem_nonunits_iff]
      exact hgnu
    rw [hunif] at hc𝔪
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hc𝔪

    have hπF : algebraMap ↥A₀ F π₀ ≠ 0 := by
      rw [halg]
      exact (map_ne_zero_iff _ (algebraMap L F).injective).mpr (fun h => hπ0 (Subtype.ext h))
    have h1 : algebraMap L F c⁻¹ = algebraMap ↥A₀ F a * algebraMap ↥A₀ F π₀ := by
      rw [← map_mul, ha, halg]
    have hc' : algebraMap L F c ≠ 0 := (map_ne_zero_iff _ (algebraMap L F).injective).mpr hc0
    have h2 : (c • f) * algebraMap L F c⁻¹ = f := by
      rw [hcf, map_inv₀, mul_comm, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
    have key : (c • f) * algebraMap ↥A₀ F a = f * (algebraMap ↥A₀ F π₀)⁻¹ := by
      calc (c • f) * algebraMap ↥A₀ F a
          = (c • f) * algebraMap ↥A₀ F a * (algebraMap ↥A₀ F π₀ * (algebraMap ↥A₀ F π₀)⁻¹) := by
            rw [mul_inv_cancel₀ hπF, mul_one]
        _ = (c • f) * (algebraMap ↥A₀ F a * algebraMap ↥A₀ F π₀) * (algebraMap ↥A₀ F π₀)⁻¹ := by ring
        _ = (c • f) * algebraMap L F c⁻¹ * (algebraMap ↥A₀ F π₀)⁻¹ := by rw [h1]
        _ = f * (algebraMap ↥A₀ F π₀)⁻¹ := by rw [h2]
    rw [← key]
    exact R.integers.mul_mem _ _ hc (hRV a)
  exact ⟨hRV, hϖV, hjV, hunr⟩

end GaussExistsUnram_node13

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'q : ℓ' ≠ q) (hℓ'3 : 3 ≤ ℓ') (hℓ'M' : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))

    (K'' : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK'' : K'' = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K''] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K'']
    (j'' : ↥K'') (hj'' : ((j'' : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j'' ≠ 0)] :
    ∀ V V' : ValuationSubring ↥K'',
      (∀ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K'' r ∈ V) →
      algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K'' ⟨π₀, hπ⟩ ∈ V.nonunits →
      (∀ P : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ¬ (Polynomial.C (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∣ P) →
        Polynomial.aeval j'' P ∈ V ∧ (Polynomial.aeval j'' P)⁻¹ ∈ V) →
      (∀ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K'' r ∈ V') →
      algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K'' ⟨π₀, hπ⟩ ∈ V'.nonunits →
      (∀ P : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ¬ (Polynomial.C (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∣ P) →
        Polynomial.aeval j'' P ∈ V' ∧ (Polynomial.aeval j'' P)⁻¹ ∈ V') →
      V = V'  := by
  classical
  haveI := hdvr
  intro V V' hV hϖV hxV hV' hϖV' hxV'

  have hXH : ModularCurve.xHFunctionField (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M') =
      qExpFunctionFieldC ℚ (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')) := rfl
  rw [hXH] at hK''
  subst hK''
  obtain ⟨R, hRmem, hRres⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
    (↥k₀) (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
    (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')) (translation_mem_GammaH _ _)
  have hmapA : coeffMap (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).subtype
      (jqModC ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = coeffEmb ↥k₀ jq := by
    change (jqModC ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).map _ = (jqModC ℚ).map (algebraMap ℚ ↥k₀)
    rw [map_jqModC, map_jqModC]
  have hy : coeffMap (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).subtype (jqModC ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈
      laurentBaseChange ↥k₀ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M'))) := by
    rw [hmapA, ← hj'']; exact j''.2
  obtain ⟨hO, hres⟩ := hRres _ hy
  have hjeq : j'' = ⟨_, hy⟩ := Subtype.ext (hj''.trans hmapA.symm)
  have hjO : (j'' : ↥(laurentBaseChange ↥k₀ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M'))))) ∈ R.integers := by
    rw [hjeq]; exact hO
  have hresj : ((R.residue ⟨j'', hjO⟩ : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
      (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))) :
        LaurentSeries (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) = jqModC _ := by
    have h1 : (⟨j'', hjO⟩ : ↥R.integers) = ⟨_, hO⟩ := Subtype.ext hjeq
    rw [h1, hres]
    change (jqModC ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).map _ = _
    exact map_jqModC _
  have hjt : Transcendental (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (R.residue ⟨j'', hjO⟩) :=
    GaussExistsUnram_node13.transcendental_of_coe_eq_jqModC _ _ _ hresj
  have hπ0 : (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
    rw [hunif, h, Ideal.span_singleton_eq_bot]

  obtain ⟨hRV₀, hϖV₀, hjV₀, -⟩ := GaussExistsUnram_node13.gaussType_and_unramified
    (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) R ⟨π₀, hπ⟩ hunif hπ0 j'' hjO hjt

  have hjq : ((j'' : LaurentSeries ↥k₀)) = jqModC ↥k₀ := by
    rw [hj'']
    change (jqModC ℚ).map (algebraMap ℚ ↥k₀) = _
    exact map_jqModC _
  have hgen := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat (↥k₀)
      (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M') j'' hjq
  have hidx : 0 < (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M') ⊔
      Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)).index := by
    have hle : CongruenceSubgroup.Gamma (ℓ' ^ 2 * M') ≤ CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M') := by
      intro A hA
      rw [CohCarrier.mem_GammaH_iff]
      have hA' := CongruenceSubgroup.Gamma_mem.mp hA
      have h0 : A ∈ CongruenceSubgroup.Gamma0 (ℓ' ^ 2 * M') := by rw [CongruenceSubgroup.Gamma0_mem]; exact hA'.2.2.1
      refine ⟨h0, ?_⟩
      have : CohCarrier.gamma0Units (ℓ' ^ 2 * M') ⟨A, h0⟩ = 1 := by
        ext
        rw [CohCarrier.val_gamma0Units]
        show ((A 1 1 : ℤ) : ZMod (ℓ' ^ 2 * M')) = ((1 : (ZMod (ℓ' ^ 2 * M'))ˣ) : ZMod (ℓ' ^ 2 * M'))
        rw [hA'.2.2.2, Units.val_one]
      rw [this]
      exact one_mem _
    haveI : (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')).FiniteIndex :=
      Subgroup.finiteIndex_of_le hle
    haveI : (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M') ⊔
        Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)).FiniteIndex :=
      Subgroup.finiteIndex_of_le le_sup_left
    exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin ↥k₀ ({j''} : Set ↥(laurentBaseChange ↥k₀ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))))) ↥(laurentBaseChange ↥k₀ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))) :=
    Module.finite_of_finrank_pos (hgen ▸ hidx)
  obtain ⟨-, hle⟩ := AlgebraicCurve.RegularProlongation.finiteDimensional_and_finrank_adjoin_residue_le R ⟨j'', hjO⟩ hjt
  have hqM : ¬ q ∣ ℓ' ^ 2 * M' := by
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : q.Prime)).mp h with h2 | h2
    · exact hℓ'q ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : ℓ'.Prime)).mp
        ((Fact.out : q.Prime).dvd_of_dvd_pow h2)).symm
    · exact hqM' h2
  have hge := ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap q (ℓ' ^ 2 * M')
      (ModularCurve.FullLevel.levelH ℓ' M') hqM A hA k₀ hκ (R.residue ⟨j'', hjO⟩) hresj
  have hdeg : Module.finrank ↥(IntermediateField.adjoin ↥k₀ ({((⟨j'', hjO⟩ : ↥R.integers) : ↥(laurentBaseChange ↥k₀ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))))} : Set ↥(laurentBaseChange ↥k₀ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))))) ↥(laurentBaseChange ↥k₀ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))) =
      Module.finrank ↥(IntermediateField.adjoin (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
        ({R.residue ⟨j'', hjO⟩} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
          (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))))
        ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M'))) :=
    le_antisymm (by rw [show ((⟨j'', hjO⟩ : ↥R.integers) : ↥(laurentBaseChange ↥k₀ (qExpFunctionFieldC ℚ (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M'))))) = j'' from rfl, hgen]; exact hge) hle
  have hfin : 0 < Module.finrank ↥(IntermediateField.adjoin (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
        ({R.residue ⟨j'', hjO⟩} : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
          (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M')))))
        ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (CohCarrier.GammaH (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M'))) :=
    lt_of_lt_of_le hidx hge

  have e1 : V = R.integers :=
    AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
      R ⟨j'', hjO⟩ hjt hfin hdeg V
      (ValuationSubring.mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem (↥k₀) (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
        ⟨π₀, hπ⟩ hunif _ j'' V R.integers hV hϖV hxV hRV₀ hϖV₀ hjV₀)
  have e2 : V' = R.integers :=
    AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
      R ⟨j'', hjO⟩ hjt hfin hdeg V'
      (ValuationSubring.mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem (↥k₀) (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
        ⟨π₀, hπ⟩ hunif _ j'' V' R.integers hV' hϖV' hxV' hRV₀ hϖV₀ hjV₀)
  exact e1.trans e2.symm

end S_ModularCurve_FullLevel_valuationSubring_eq_of_gaussType_of_coprime_level
end P2MW
export P2MW.S_ModularCurve_FullLevel_valuationSubring_eq_of_gaussType_of_coprime_level (solution)
