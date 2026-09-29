-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_isChartAt_of_isAffineGeomPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7709528e-fc0a-5086-a0b1-a5afd37fc071

import Definitions.Def_ModularCurve_ChartSemicontinuity
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_finrankAlong_id
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_piFin_range_localizes_of_jqModC_mem
import Theorems.Thm_ModularCurve_CharPModel_exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem
import Definitions.Def_ModularCurve_FibreModel
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_CharPReduction_mem_or_inv_mem_modularLocalized
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_FrobeniusModL
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

section
open AlgebraicCurve Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff charP_modularFunctionFieldC frobOnPlacesGeomLevel_surjective KroneckerCongruence jGeomGen jNGeomGen coe_jNGeomGen IsAffineGeomPlace jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin modularFunctionFieldBar_eq_modularFunctionFieldC exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs finrankAlong_heckeBetaBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem CharPReduction.modularRedLocHom_mem adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional"
namespace ChartGen
p2m_open "ModularCurve~jBar"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
  [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
variable (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)

section Coordinates

variable {E : IntermediateField L F} (hE₂ : ∀ e ∈ E, e ∈ R₁.integers → e ∈ R₂.integers)
  (σ : Fb₁ →+* Fb₂)
  (hσ : ∀ e (he : e ∈ E) (h₁ : e ∈ R₁.integers), R₂.residue ⟨e, hE₂ e he h₁⟩ = σ (R₁.residue ⟨e, h₁⟩))
  {q : ℕ} (hq : q.Prime) [CharP Fb₂ q] (hpi : ∀ y : Fb₂, y ^ q ∈ σ.range)
  {z : F} (hz₁ : z ∈ R₁.integers) (hz₂ : z ∈ R₂.integers)
  (hzr₂ : R₂.residue ⟨z, hz₂⟩ ∉ σ.range)

include hσ hq hpi hz₁ hzr₂ in

private theorem residue_coeff_eq_zero_of_residues_eq_zero (γ : Fin (q + 1) → F) (hγE : ∀ i, γ i ∈ E)
    (hγ₁ : ∀ i, γ i ∈ R₁.integers) {θ : F} (hθ : θ = ∑ i, γ i * z ^ (i : ℕ))
    (hθ₁ : θ ∈ R₁.integers) (hθ₂ : θ ∈ R₂.integers)
    (h₁ : R₁.residue ⟨θ, hθ₁⟩ = 0) (h₂ : R₂.residue ⟨θ, hθ₂⟩ = 0) :
    ∀ i, R₁.residue ⟨γ i, hγ₁ i⟩ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq.pos).symm⟩

  obtain ⟨η, hη⟩ := RingHom.mem_range.mp (hpi (R₂.residue ⟨z, hz₂⟩))
  haveI : Fact (m + 1).Prime := ⟨hq⟩
  have hfrob : ∀ a b : Fb₂, a ^ (m + 1) = b ^ (m + 1) → a = b := by
    intro a b hab
    have h : (a - b) ^ (m + 1) = a ^ (m + 1) - b ^ (m + 1) := by rw [sub_pow_char]
    rw [hab, sub_self] at h
    exact sub_eq_zero.mp (pow_eq_zero_iff (Nat.succ_ne_zero m) |>.mp h)
  have hηq : ∀ b : Fb₁, b ^ (m + 1) ≠ η := by
    intro b hb
    apply hzr₂
    refine RingHom.mem_range.mpr ⟨b, hfrob _ _ ?_⟩
    rw [← map_pow, hb, hη]
  have hζ : R₁.residue ⟨z, hz₁⟩ ^ (m + 1) ≠ η := by
    intro hc
    apply hzr₂
    refine RingHom.mem_range.mpr ⟨R₁.residue ⟨z, hz₁⟩, hfrob _ _ ?_⟩
    rw [← map_pow, hc, hη]
  set xb := η with hxb
  set ζ := R₁.residue ⟨z, hz₁⟩ with hζdef
  set ξ := R₂.residue ⟨z, hz₂⟩ with hξ
  set δ : Fin (m + 1 + 1) → Fb₁ := fun i => R₁.residue ⟨γ i, hγ₁ i⟩ with hδ

  have hI : ∑ i, δ i * ζ ^ (i : ℕ) = 0 := by
    have hsub : (⟨θ, hθ₁⟩ : R₁.integers) = ∑ i : Fin (m + 1 + 1), ⟨γ i, hγ₁ i⟩ * ⟨z, hz₁⟩ ^ (i : ℕ) := by
      apply Subtype.ext
      push_cast
      exact hθ
    rw [hsub, map_sum] at h₁
    simpa only [map_mul, map_pow] using h₁
  have hII : ∑ i, σ (δ i) * ξ ^ (i : ℕ) = 0 := by
    have hsub : (⟨θ, hθ₂⟩ : R₂.integers)
        = ∑ i : Fin (m + 1 + 1), ⟨γ i, hE₂ (γ i) (hγE i) (hγ₁ i)⟩ * ⟨z, hz₂⟩ ^ (i : ℕ) := by
      apply Subtype.ext
      push_cast
      exact hθ
    rw [hsub, map_sum] at h₂
    simp only [map_mul, map_pow] at h₂
    rw [← h₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hσ (γ i) (hγE i) (hγ₁ i), hδ, hξ]

  letI : Algebra Fb₁ Fb₂ := σ.toAlgebra
  have hmin : minpoly Fb₁ ξ = X ^ (m + 1) - C xb := by
    refine (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hq hηq) ?_
      (monic_X_pow_sub_C xb (Nat.succ_ne_zero m))).symm
    simp [RingHom.algebraMap_toAlgebra, hη]
  have hli : LinearIndependent Fb₁ fun i : Fin (m + 1) => ξ ^ (i : ℕ) := by
    have h := linearIndependent_pow (K := Fb₁) ξ
    rwa [hmin, natDegree_X_pow_sub_C] at h

  set g : Fin (m + 1) → Fb₁ :=
    fun i => δ (Fin.castSucc i) + if i = 0 then δ (Fin.last _) * xb else 0 with hg
  have hg0 : ∀ i, g i = 0 := by
    refine Fintype.linearIndependent_iff.mp hli g ?_
    simp only [hg, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_add, add_mul, Finset.sum_add_distrib]
    rw [Fin.sum_univ_castSucc] at hII
    have hlast : σ (δ (Fin.last (m + 1))) * ξ ^ ((Fin.last (m + 1) : ℕ)) = σ (δ (Fin.last _) * xb) := by
      rw [Fin.val_last, ← hη, map_mul]
    rw [hlast] at hII
    convert hII using 2
    all_goals first
      | rfl
      | (rw [Finset.sum_eq_single (0 : Fin (m + 1)) (fun b _ hb => by simp [hb])
          (fun h => absurd (Finset.mem_univ _) h)]; simp)
      | simp [Fin.coe_castSucc]
  have hmid : ∀ i : Fin (m + 1), i ≠ 0 → δ (Fin.castSucc i) = 0 := by
    intro i hi
    simpa [hg, hi] using hg0 i
  have h0 : δ 0 = -(δ (Fin.last _) * xb) := by
    have h := hg0 0
    simp only [hg, if_true, Fin.castSucc_zero] at h
    exact eq_neg_of_add_eq_zero_left h

  have hlastzero : δ (Fin.last _) = 0 := by
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_single (0 : Fin (m + 1))] at hI
    · simp only [Fin.castSucc_zero, Fin.val_zero, pow_zero, mul_one, Fin.val_last, h0] at hI
      have hI' : δ (Fin.last _) * (ζ ^ (m + 1) - xb) = 0 := by
        rw [mul_sub]
        linear_combination hI
      exact (mul_eq_zero.mp hI').resolve_right (sub_ne_zero.mpr hζ)
    · intro b _ hb
      rw [hmid b hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  intro i
  show δ i = 0
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · by_cases hj : j = 0
    · subst hj
      rw [Fin.castSucc_zero, h0, hlastzero, zero_mul, neg_zero]
    · exact hmid j hj
  · exact hlastzero

end Coordinates

section Gauss

variable {E : IntermediateField L F} (hE₂ : ∀ e ∈ E, e ∈ R₁.integers → e ∈ R₂.integers)
  (σ : Fb₁ →+* Fb₂)
  (hσ : ∀ e (he : e ∈ E) (h₁ : e ∈ R₁.integers), R₂.residue ⟨e, hE₂ e he h₁⟩ = σ (R₁.residue ⟨e, h₁⟩))
  {q : ℕ} (hq : q.Prime) [CharP Fb₂ q] (hpi : ∀ y : Fb₂, y ^ q ∈ σ.range)
  {z : F} (hz₁ : z ∈ R₁.integers) (hz₂ : z ∈ R₂.integers)
  (hzr₂ : R₂.residue ⟨z, hz₂⟩ ∉ σ.range)

private theorem const_smul_mem {c : L} (hc : c ∈ A) {f : F} (hf : f ∈ R₁.integers) :
    c • f ∈ R₁.integers := by
  rw [Algebra.smul_def]
  exact mul_mem ((R₁.algebraMap_mem_iff c).mpr hc) hf

include hσ hq hpi hz₁ hzr₂ in

private theorem coeff_mem_integers_of_mem_integers (γ : Fin (q + 1) → F) (hγE : ∀ i, γ i ∈ E) {h : F}
    (hh : h = ∑ i, γ i * z ^ (i : ℕ)) (hh₁ : h ∈ R₁.integers) (hh₂ : h ∈ R₂.integers) :
    ∀ i, γ i ∈ R₁.integers := by
  classical
  by_cases hzero : ∀ i, γ i = 0
  · intro i
    rw [hzero i]
    exact zero_mem _
  obtain ⟨i₁, hi₁⟩ := not_forall.mp hzero

  have hsc : ∀ i, ∃ c : L, ∃ hc : c • γ i ∈ R₁.integers, γ i ≠ 0 → R₁.residue ⟨c • γ i, hc⟩ ≠ 0 := by
    intro i
    by_cases hi : γ i = 0
    · exact ⟨1, by rw [hi, smul_zero]; exact zero_mem _, fun h => absurd hi h⟩
    · obtain ⟨c, hc, hres⟩ := R₁.exists_smul_mem (γ i) hi
      exact ⟨c, hc, fun _ => hres⟩
  choose cs hcs hcsres using hsc
  have hcs0 : ∀ i, γ i ≠ 0 → cs i ≠ 0 := fun i hi => R₁.smul_const_ne_zero (hcs i) (hcsres i hi)

  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i => γ i ≠ 0)
    (fun i => A.valuation (cs i)) ⟨i₁, by simpa using hi₁⟩
  have hγi₀ : γ i₀ ≠ 0 := by simpa using hi₀
  set c := cs i₀ with hc
  have hc0 : c ≠ 0 := hcs0 i₀ hγi₀

  have hcγ : ∀ i, c • γ i ∈ R₁.integers := by
    intro i
    by_cases hi : γ i = 0
    · rw [hi, smul_zero]; exact zero_mem _
    have hdiv : c / cs i ∈ A := by
      rw [← A.valuation_le_one_iff, map_div₀,
        div_le_one₀ (by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr (hcs0 i hi))]
      exact hmin i (by simpa using hi)
    have : c • γ i = (c / cs i) • (cs i • γ i) := by
      rw [smul_smul, div_mul_cancel₀ _ (hcs0 i hi)]
    rw [this]
    exact const_smul_mem R₁ hdiv (hcs i)
  rcases A.mem_or_inv_mem c with hcA | hcinv
  swap
  ·
    intro i
    have : γ i = c⁻¹ • (c • γ i) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact const_smul_mem R₁ hcinv (hcγ i)

  by_cases hunit : c⁻¹ ∈ A
  · intro i
    have : γ i = c⁻¹ • (c • γ i) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact const_smul_mem R₁ hunit (hcγ i)
  exfalso
  have hcmax : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hunit
    have hmul : ((u⁻¹ : Aˣ) : A) * ⟨c, hcA⟩ = 1 := by rw [← hu, Units.inv_mul]
    have hmul' : ((u⁻¹ : Aˣ) : L) * c = 1 := by
      have h := congrArg (fun a : A => (a : L)) hmul
      simpa using h
    rw [← eq_inv_of_mul_eq_one_left hmul']
    exact ((u⁻¹ : Aˣ) : A).2
  have hcres : IsLocalRing.residue A ⟨c, hcA⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hcmax

  set θ := c • h with hθdef
  have hθ : θ = ∑ i, (c • γ i) * z ^ (i : ℕ) := by
    rw [hθdef, hh, Finset.smul_sum]
    simp only [smul_mul_assoc]
  have hθ₁ : θ ∈ R₁.integers := const_smul_mem R₁ hcA hh₁
  have hθ₂ : θ ∈ R₂.integers := by
    rw [hθdef, Algebra.smul_def]
    exact mul_mem ((R₂.algebraMap_mem_iff c).mpr hcA) hh₂
  have hres₁ : R₁.residue ⟨θ, hθ₁⟩ = 0 := by
    have hsub : (⟨θ, hθ₁⟩ : R₁.integers)
        = ⟨algebraMap L F c, (R₁.algebraMap_mem_iff c).mpr hcA⟩ * ⟨h, hh₁⟩ := by
      apply Subtype.ext
      simp [hθdef, Algebra.smul_def]
    rw [hsub, map_mul, R₁.residue_algebraMap ⟨c, hcA⟩, hcres, map_zero, zero_mul]
  have hres₂ : R₂.residue ⟨θ, hθ₂⟩ = 0 := by
    have hsub : (⟨θ, hθ₂⟩ : R₂.integers)
        = ⟨algebraMap L F c, (R₂.algebraMap_mem_iff c).mpr hcA⟩ * ⟨h, hh₂⟩ := by
      apply Subtype.ext
      simp [hθdef, Algebra.smul_def]
    rw [hsub, map_mul, R₂.residue_algebraMap ⟨c, hcA⟩, hcres, map_zero, zero_mul]
  have hall := residue_coeff_eq_zero_of_residues_eq_zero R₁ R₂ hE₂ σ hσ hq hpi hz₁ hz₂ hzr₂
    (fun i => c • γ i) (fun i => E.smul_mem (hγE i)) hcγ hθ hθ₁ hθ₂ hres₁ hres₂ i₀
  exact hcsres i₀ hγi₀ hall

include hσ hq hpi hz₁ hzr₂ in

private theorem eq_zero_of_sum_mul_pow_eq_zero (γ : Fin (q + 1) → F) (hγE : ∀ i, γ i ∈ E)
    (hsum : ∑ i, γ i * z ^ (i : ℕ) = 0) : ∀ i, γ i = 0 := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
  set γ' : Fin (q + 1) → F := fun i => (γ i₀)⁻¹ * γ i with hγ'
  have hγ'E : ∀ i, γ' i ∈ E := fun i => E.mul_mem (E.inv_mem (hγE i₀)) (hγE i)
  have hsum' : (0 : F) = ∑ i, γ' i * z ^ (i : ℕ) := by
    simp only [hγ', mul_assoc, ← Finset.mul_sum, hsum, mul_zero]
  have hγ'₁ := coeff_mem_integers_of_mem_integers R₁ R₂ hE₂ σ hσ hq hpi hz₁ hz₂ hzr₂ γ' hγ'E hsum'
    (zero_mem _) (zero_mem _)
  have hres := residue_coeff_eq_zero_of_residues_eq_zero R₁ R₂ hE₂ σ hσ hq hpi hz₁ hz₂ hzr₂ γ' hγ'E hγ'₁
    hsum' (zero_mem _) (zero_mem _) (map_zero _) (map_zero _) i₀
  have h1 : γ' i₀ = 1 := inv_mul_cancel₀ hi₀
  have hone : (⟨γ' i₀, hγ'₁ i₀⟩ : R₁.integers) = 1 := Subtype.ext h1
  rw [hone, map_one] at hres
  exact one_ne_zero hres

end Gauss

end ModularCurve.ChartGen

end

section
open AlgebraicCurve Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff charP_modularFunctionFieldC frobOnPlacesGeomLevel_surjective KroneckerCongruence jGeomGen jNGeomGen coe_jNGeomGen IsAffineGeomPlace jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin modularFunctionFieldBar_eq_modularFunctionFieldC exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs finrankAlong_heckeBetaBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem CharPReduction.modularRedLocHom_mem adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional"
namespace ChartGen
p2m_open "ModularCurve~jBar"

private theorem map_derivative_eval {S T : Type*} [CommRing S] [CommRing T] (ρ : S →+* T) (p : Polynomial S)
    (a : S) : ρ ((derivative p).eval a) = (derivative (p.map ρ)).eval (ρ a) := by
  rw [derivative_map, eval_map, eval₂_at_apply]

private theorem map_eval' {S T : Type*} [CommRing S] [CommRing T] (ρ : S →+* T) (p : Polynomial S) (a : S) :
    ρ (p.eval a) = (p.map ρ).eval (ρ a) := by
  rw [eval_map, eval₂_at_apply]

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
  [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
variable (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
variable {E : IntermediateField L F} (hE₂ : ∀ e ∈ E, e ∈ R₁.integers → e ∈ R₂.integers)
  (σ : Fb₁ →+* Fb₂)
  (hσ : ∀ e (he : e ∈ E) (h₁ : e ∈ R₁.integers), R₂.residue ⟨e, hE₂ e he h₁⟩ = σ (R₁.residue ⟨e, h₁⟩))
  {q : ℕ} (hq : q.Prime) [CharP Fb₂ q] (hpi : ∀ y : Fb₂, y ^ q ∈ σ.range)
  {z : F} (hz₂ : z ∈ R₂.integers) (hzr₂ : R₂.residue ⟨z, hz₂⟩ ∉ σ.range)

include hσ hq hpi hzr₂ in

private theorem core (P₁ : Polynomial R₁.integers) (hPE : ∀ i, ((P₁.coeff i : R₁.integers) : F) ∈ E)
    (hroot : (P₁.map R₁.integers.subtype).eval z = 0) :
    ∃ (η : Fb₁) (Q : Polynomial Fb₁), σ η = R₂.residue ⟨z, hz₂⟩ ^ q ∧
      P₁.map R₁.residue = (X ^ q - C η) * Q ∧
      ∃ hD : (derivative (P₁.map R₁.integers.subtype)).eval z ∈ R₂.integers,
        R₂.residue ⟨_, hD⟩ = (derivative ((P₁.map R₁.residue).map σ)).eval (R₂.residue ⟨z, hz₂⟩) := by
  set P : Polynomial F := P₁.map R₁.integers.subtype with hPdef
  have hc₁ : ∀ i, ((P₁.coeff i : R₁.integers) : F) = P.coeff i := fun i => by
    rw [hPdef, coeff_map]
    rfl

  obtain ⟨P₂, hP₂map⟩ := (mem_lifts (f := R₂.integers.subtype) P).mp
    ((lifts_iff_coeff_lifts (f := R₂.integers.subtype) P).mpr
      fun i => ⟨⟨P.coeff i, hE₂ _ (hc₁ i ▸ hPE i) (hc₁ i ▸ (P₁.coeff i).2)⟩, rfl⟩)
  have hc₂ : ∀ i, ((P₂.coeff i : R₂.integers) : F) = P.coeff i := fun i => by
    rw [← hP₂map, coeff_map]
    rfl
  set zI : R₂.integers := ⟨z, hz₂⟩ with hzI

  have hbar : P₂.map R₂.residue = (P₁.map R₁.residue).map σ := by
    ext i
    rw [coeff_map, coeff_map, coeff_map]
    have h₂ : P₂.coeff i = ⟨P.coeff i, hE₂ _ (hc₁ i ▸ hPE i) (hc₁ i ▸ (P₁.coeff i).2)⟩ :=
      Subtype.ext (hc₂ i)
    have h₁ : P₁.coeff i = ⟨P.coeff i, hc₁ i ▸ (P₁.coeff i).2⟩ := Subtype.ext (hc₁ i)
    rw [h₁, h₂]
    exact hσ (P.coeff i) (hc₁ i ▸ hPE i) (hc₁ i ▸ (P₁.coeff i).2)

  have hroot₂ : (P₂.map R₂.residue).eval (R₂.residue zI) = 0 := by
    have h0 : P₂.eval zI = 0 := by
      apply Subtype.ext
      have h := map_eval' R₂.integers.subtype P₂ zI
      rw [hP₂map] at h
      exact h.trans hroot
    rw [← map_eval', h0, map_zero]

  letI : Algebra Fb₁ Fb₂ := σ.toAlgebra
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨η, hη⟩ := RingHom.mem_range.mp (hpi (R₂.residue zI))
  have hfrob : ∀ a b : Fb₂, a ^ q = b ^ q → a = b := by
    intro a b hab
    have h : (a - b) ^ q = a ^ q - b ^ q := by rw [sub_pow_char]
    rw [hab, sub_self] at h
    exact sub_eq_zero.mp ((pow_eq_zero_iff hq.ne_zero).mp h)
  have hηq : ∀ b : Fb₁, b ^ q ≠ η := by
    intro b hb
    apply hzr₂
    refine RingHom.mem_range.mpr ⟨b, hfrob _ _ ?_⟩
    rw [← map_pow, hb, hη]
  have hmin : minpoly Fb₁ (R₂.residue zI) = X ^ q - C η := by
    refine (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hq hηq) ?_
      (monic_X_pow_sub_C η hq.ne_zero)).symm
    simp [RingHom.algebraMap_toAlgebra, hη]
  have haeval : aeval (R₂.residue zI) (P₁.map R₁.residue) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, RingHom.algebraMap_toAlgebra, ← hbar]
    exact hroot₂
  have hdvd := minpoly.dvd Fb₁ (R₂.residue zI) haeval
  rw [hmin] at hdvd
  obtain ⟨Q, hQ⟩ := hdvd

  have hDeq : (derivative P).eval z = (((derivative P₂).eval zI : R₂.integers) : F) := by
    rw [← hP₂map]
    exact (map_derivative_eval R₂.integers.subtype P₂ zI).symm
  have hmem : (derivative P).eval z ∈ R₂.integers := hDeq ▸ ((derivative P₂).eval zI).2
  refine ⟨η, Q, hη, hQ, hmem, ?_⟩
  have hel : (⟨(derivative P).eval z, hmem⟩ : R₂.integers) = (derivative P₂).eval zI := Subtype.ext hDeq
  rw [hel, map_derivative_eval, hbar]

include hσ hq hpi hzr₂ in

private theorem exists_mem_and_residue_derivative_eval_eq_zero (P : Polynomial F) (hPE : ∀ i, P.coeff i ∈ E)
    (hP₁ : ∀ i, P.coeff i ∈ R₁.integers) (hroot : P.eval z = 0) :
    ∃ hD : (derivative P).eval z ∈ R₂.integers, R₂.residue ⟨_, hD⟩ = 0 := by
  obtain ⟨P₁, rfl⟩ := (mem_lifts (f := R₁.integers.subtype) P).mp
    ((lifts_iff_coeff_lifts (f := R₁.integers.subtype) P).mpr fun i => ⟨⟨P.coeff i, hP₁ i⟩, rfl⟩)
  have hPE' : ∀ i, ((P₁.coeff i : R₁.integers) : F) ∈ E := fun i => by
    have h := hPE i
    rw [coeff_map] at h
    exact h
  obtain ⟨η, Q, hη, hQ, hD, hres⟩ := core R₁ R₂ hE₂ σ hσ hq hpi hz₂ hzr₂ P₁ hPE' hroot
  refine ⟨hD, ?_⟩
  rw [hres, hQ, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    derivative_mul, eval_add, eval_mul, eval_mul, eval_sub, eval_pow, eval_X, eval_C, hη, sub_self, zero_mul,
    add_zero, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C,
    CharP.cast_eq_zero Fb₂ q, zero_mul, zero_mul]

include hσ hq hpi hzr₂ in

private theorem exists_residue_derivative_eval_eq_pow_sub (hz₁ : z ∈ R₁.integers) (P : Polynomial F)
    (hPE : ∀ i, P.coeff i ∈ E) (hP₁ : ∀ i, P.coeff i ∈ R₁.integers) (hmonic : P.Monic)
    (hdeg : P.natDegree = q + 1) (hroot : P.eval z = 0) :
    ∃ η : Fb₁, σ η = R₂.residue ⟨z, hz₂⟩ ^ q ∧
      ∀ hD : (derivative P).eval z ∈ R₁.integers, R₁.residue ⟨_, hD⟩ = R₁.residue ⟨z, hz₁⟩ ^ q - η := by
  obtain ⟨P₁, rfl, hP₁deg, hP₁monic⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := R₁.integers.subtype) P).mpr fun i => ⟨⟨P.coeff i, hP₁ i⟩, rfl⟩) hmonic
  have hPE' : ∀ i, ((P₁.coeff i : R₁.integers) : F) ∈ E := fun i => by
    have h := hPE i
    rw [coeff_map] at h
    exact h
  obtain ⟨η, Q, hη, hQ, -, -⟩ := core R₁ R₂ hE₂ σ hσ hq hpi hz₂ hzr₂ P₁ hPE' hroot
  refine ⟨η, hη, fun hD => ?_⟩

  have hbar_monic : (P₁.map R₁.residue).Monic := hP₁monic.map _
  have hXq : (X ^ q - C η : Polynomial Fb₁).Monic := monic_X_pow_sub_C η hq.ne_zero
  have hQmonic : Q.Monic := hXq.of_mul_monic_left (hQ ▸ hbar_monic)
  have hQdeg : Q.natDegree = 1 := by
    have h := congrArg natDegree hQ
    rw [hP₁monic.natDegree_map, hP₁deg, hdeg, hXq.natDegree_mul hQmonic, natDegree_X_pow_sub_C] at h
    omega
  have hq1 : ((q : ℕ) : Fb₁) = 0 := by
    apply σ.injective
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero Fb₂ q

  set zI₁ : R₁.integers := ⟨z, hz₁⟩ with hzI₁
  have hDeq : (derivative (P₁.map R₁.integers.subtype)).eval z = (((derivative P₁).eval zI₁ : R₁.integers) : F) :=
    (map_derivative_eval R₁.integers.subtype P₁ zI₁).symm
  have hel : (⟨(derivative (P₁.map R₁.integers.subtype)).eval z, hD⟩ : R₁.integers) = (derivative P₁).eval zI₁ :=
    Subtype.ext hDeq
  rw [hel, map_derivative_eval, hQ, hQmonic.eq_X_add_C hQdeg, derivative_mul, derivative_X_add_C, eval_add,
    eval_mul, eval_mul, eval_one, mul_one, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul,
    eval_C, hq1, zero_mul, zero_mul, zero_add, eval_sub, eval_pow, eval_X, eval_C]

end ModularCurve.ChartGen
end

section
open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff charP_modularFunctionFieldC frobOnPlacesGeomLevel_surjective KroneckerCongruence jGeomGen jNGeomGen coe_jNGeomGen IsAffineGeomPlace jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin modularFunctionFieldBar_eq_modularFunctionFieldC exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs finrankAlong_heckeBetaBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem CharPReduction.modularRedLocHom_mem adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional"
namespace ChartGen
p2m_open "ModularCurve~jBar"

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

private theorem natCast_mem_nonunits_of_charP {k : Type*} [Field k] {q : ℕ} [CharP k q] (red : A →+* k) :
    ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
  have hqA : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    have h' := h.map red
    rw [map_natCast, CharP.cast_eq_zero k q] at h'
    exact not_isUnit_zero h'
  have h := (ValuationSubring.coe_mem_nonunits_iff (A := A) (a := ((q : ℕ) : A))).mpr hqA
  simpa using h

variable {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb] (R : RegularProlongation A F Fb)

private theorem const_smul_mem' {c : AlgebraicClosure ℚ} (hc : c ∈ A) {f : F} (hf : f ∈ R.integers) :
    c • f ∈ R.integers := by
  rw [Algebra.smul_def]
  exact mul_mem ((R.algebraMap_mem_iff c).mpr hc) hf

private theorem exists_const_smul_mem (f : F) : ∃ d : A, d ≠ 0 ∧ (d : AlgebraicClosure ℚ) • f ∈ R.integers := by
  by_cases hf : f = 0
  · exact ⟨1, one_ne_zero, by rw [hf, smul_zero]; exact zero_mem _⟩
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hres
  rcases A.mem_or_inv_mem c with hcA | hcinv
  · exact ⟨⟨c, hcA⟩, fun h => hc0 (congrArg Subtype.val h), hc⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    have : f = c⁻¹ • (c • f) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [OneMemClass.coe_one, one_smul, this]
    exact const_smul_mem' R hcinv hc

private theorem exists_const_smul_eq_of_residue_eq_zero {g : F} (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ = 0)
    (hgne : g ≠ 0) :
    ∃ (c : A) (u : F) (hu : u ∈ R.integers),
      c ∈ IsLocalRing.maximalIdeal A ∧ c ≠ 0 ∧ R.residue ⟨u, hu⟩ ≠ 0 ∧ g = (c : AlgebraicClosure ℚ) • u := by
  obtain ⟨c₁, hc₁, hres⟩ := R.exists_smul_mem g hgne
  have hc₁0 : c₁ ≠ 0 := R.smul_const_ne_zero hc₁ hres

  have hinv : c₁⁻¹ ∈ A := by
    by_contra hnot
    have hc₁A : c₁ ∈ A := (A.mem_or_inv_mem c₁).resolve_right hnot
    apply hres
    have hsub : (⟨c₁ • g, hc₁⟩ : R.integers)
        = ⟨algebraMap (AlgebraicClosure ℚ) F c₁, (R.algebraMap_mem_iff c₁).mpr hc₁A⟩ * ⟨g, hg⟩ := by
      apply Subtype.ext
      simp [Algebra.smul_def]
    rw [hsub, map_mul, hg0, mul_zero]
  have hgeq : g = c₁⁻¹ • (c₁ • g) := by rw [smul_smul, inv_mul_cancel₀ hc₁0, one_smul]
  refine ⟨⟨c₁⁻¹, hinv⟩, c₁ • g, hc₁, ?_, fun h => inv_ne_zero hc₁0 (congrArg Subtype.val h), hres, hgeq⟩

  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsub : (⟨g, hg⟩ : R.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) F c₁⁻¹, (R.algebraMap_mem_iff c₁⁻¹).mpr hinv⟩ * ⟨c₁ • g, hc₁⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    rw [← Algebra.smul_def]
    exact hgeq
  have h := hg0
  rw [hsub, map_mul, R.residue_algebraMap ⟨c₁⁻¹, hinv⟩] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact (algebraMap (IsLocalRing.ResidueField A) Fb).injective (by rw [h0, map_zero])
  · exact absurd h0 hres

private theorem exists_pow_mul_mem {q : ℕ} [Fact q.Prime] (hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) (f : F)
    {g : F} (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ = 0) (hgne : g ≠ 0) :
    ∃ M : ℕ, g ^ M * f ∈ R.integers := by
  obtain ⟨d, hd0, hdf⟩ := exists_const_smul_mem R f
  obtain ⟨c, u, hu, hcm, hc0, -, rfl⟩ := exists_const_smul_eq_of_residue_eq_zero R hg hg0 hgne
  obtain ⟨M, a, ha⟩ := ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal A hq d hd0 c hcm hc0
  refine ⟨M, ?_⟩
  have hcM : (c : AlgebraicClosure ℚ) ^ M = (d : AlgebraicClosure ℚ) * (a : AlgebraicClosure ℚ) := by
    have h := congrArg (fun x : A => (x : AlgebraicClosure ℚ)) ha
    simpa using h
  have hrepr : ((c : AlgebraicClosure ℚ) • u) ^ M * f
      = (a : AlgebraicClosure ℚ) • (u ^ M * ((d : AlgebraicClosure ℚ) • f)) := by
    rw [smul_pow, hcM, mul_comm (d : AlgebraicClosure ℚ), mul_smul, smul_mul_assoc, smul_mul_assoc]
    congr 1
    rw [mul_smul_comm]
  rw [hrepr]
  exact const_smul_mem' R a.2 (mul_mem (pow_mem hu M) hdf)

end ModularCurve.ChartGen
end

section
p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff charP_modularFunctionFieldC frobOnPlacesGeomLevel_surjective KroneckerCongruence jGeomGen jNGeomGen coe_jNGeomGen IsAffineGeomPlace jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin modularFunctionFieldBar_eq_modularFunctionFieldC exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs finrankAlong_heckeBetaBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem CharPReduction.modularRedLocHom_mem adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional"
namespace ChartGen
p2m_open "ModularCurve~jBar"

private theorem finrankAlong_algEquiv_toAlgHom {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃ₐ[K] F') : finrankAlong K e.toAlgHom = 1 := by
  have h := finrankAlong_comp e.toAlgHom e.symm.toAlgHom
  have hid : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K F := by
    ext x
    simp
  rw [hid, finrankAlong_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

private theorem finrankAlong_heckeAlphaBar_of_not_dvd (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1 := by
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q σ hσ).1
  have hβ := finrankAlong_heckeBetaBar (AlgebraicClosure ℚ) N q
  rw [if_neg hqN, ← hlegs, finrankAlong_comp, finrankAlong_algEquiv_toAlgHom, mul_one] at hβ
  exact hβ

end ModularCurve.ChartGen
end

section
p2m_open "ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff charP_modularFunctionFieldC frobOnPlacesGeomLevel_surjective KroneckerCongruence jGeomGen jNGeomGen coe_jNGeomGen IsAffineGeomPlace jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin modularFunctionFieldBar_eq_modularFunctionFieldC exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs finrankAlong_heckeBetaBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem CharPReduction.modularRedLocHom_mem adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional"
namespace ChartGen
p2m_open "ModularCurve~jBar"

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

omit [NeZero N] in

private theorem coeffMap_mem_fullC (τ : K →+* K) {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldFullC K N) :
    coeffMap τ x ∈ modularFunctionFieldFullC K N := by
  change x ∈ Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ divisorExpansionsC K N) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨d, hd0, hdN, rfl⟩
      · rw [coeffMap_algebraMap]
        exact (modularFunctionFieldFullC K N).algebraMap_mem _
      · haveI := hd0
        rw [coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_jqModC]
        exact jqModCd_mem_full K N hdN
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

variable (q : ℕ) [Fact q.Prime] [CharP K q]

omit [NeZero N] in

private theorem qExpand_mem_fullC {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldFullC K N) :
    qExpand K q x ∈ modularFunctionFieldFullC K N := by
  have hle : (modularFunctionFieldFullC K N).map (qExpandAlgHomC K q) ≤ modularFunctionFieldFullC K N := by
    rw [modularFunctionFieldFullC, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨d, hd0, hdN, rfl⟩, rfl⟩
    haveI := hd0
    show qExpandAlgHomC K q (qExpand K d (jqModC K)) ∈ modularFunctionFieldFullC K N
    have hcomm : qExpand K q (qExpand K d (jqModC K)) = qExpand K d (qExpand K q (jqModC K)) := by
      rw [qExpand_qExpand, qExpand_qExpand]
      simp only [Nat.mul_comm]
    rw [qExpandAlgHomC_apply, hcomm, qExpand_jqModC_eq_pow_unconditional, map_pow]
    exact pow_mem (jqModCd_mem_full K N hdN) q
  exact hle ⟨x, hx, rfl⟩

private noncomputable def twist : modularFunctionFieldFullC K N →+* modularFunctionFieldFullC K N where
  toFun x := ⟨qExpand K q (x : LaurentSeries K), qExpand_mem_fullC K N q x.2⟩
  map_one' := Subtype.ext (map_one (qExpand K q))
  map_mul' x y := Subtype.ext (map_mul (qExpand K q) (x : LaurentSeries K) y)
  map_zero' := Subtype.ext (map_zero (qExpand K q))
  map_add' x y := Subtype.ext (map_add (qExpand K q) (x : LaurentSeries K) y)

omit [NeZero N] in
@[scoped simp]
private theorem coe_twist (x : modularFunctionFieldFullC K N) :
    (twist K N q x : LaurentSeries K) = qExpand K q (x : LaurentSeries K) :=
  rfl

omit [NeZero N] in

private theorem pow_mem_range_twist (y : modularFunctionFieldFullC K N) : y ^ q ∈ (twist K N q).range := by
  refine RingHom.mem_range.mpr ⟨⟨coeffMap (frobenius K q) (y : LaurentSeries K), coeffMap_mem_fullC K N _ y.2⟩, ?_⟩
  apply Subtype.ext
  show qExpand K q (coeffMap (frobenius K q) (y : LaurentSeries K)) = ((y ^ q : modularFunctionFieldFullC K N) :
    LaurentSeries K)
  rw [← coeffSemilinearAut.coeffMap_qExpand, ← pow_char_eq_coeffMap_frobenius_qExpand q]
  norm_cast

omit [NeZero N] in

private theorem notMem_range_twist_of_coeff_ne_zero {y : modularFunctionFieldFullC K N} {n : ℤ} (hn : ¬ (q : ℤ) ∣ n)
    (hy : (y : LaurentSeries K).coeff n ≠ 0) : y ∉ (twist K N q).range := by
  intro hmem
  obtain ⟨w, hw⟩ := RingHom.mem_range.mp hmem
  apply hy
  rw [← hw, coe_twist, qExpand_coeff_of_not_dvd q _ hn]

omit [NeZero N] in

private theorem jqModC_notMem_range_twist :
    (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ∉ (twist K N q).range := by
  refine notMem_range_twist_of_coeff_ne_zero K N q (n := -1) ?_ ?_
  · intro h
    rw [Int.dvd_neg] at h
    have h1 : q ∣ 1 := by exact_mod_cast h
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  · show (jqModC K).coeff (-1) ≠ 0
    rw [coeff_jqModC_neg_one]
    exact one_ne_zero

private theorem jqNModC_notMem_range_twist (hqN : ¬ q ∣ N) :
    (⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ : modularFunctionFieldFullC K N) ∉ (twist K N q).range := by
  refine notMem_range_twist_of_coeff_ne_zero K N q (n := -(N : ℤ)) ?_ ?_
  · intro h
    rw [Int.dvd_neg] at h
    exact hqN (by exact_mod_cast h)
  · show (qExpand K N (jqModC K)).coeff (-(N : ℤ)) ≠ 0
    rw [show (-(N : ℤ)) = (N : ℤ) * (-1) by ring, qExpand_coeff_mul, coeff_jqModC_neg_one]
    exact one_ne_zero

end ModularCurve.ChartGen
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"

section
p2m_open "Polynomial AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff charP_modularFunctionFieldC frobOnPlacesGeomLevel_surjective KroneckerCongruence jGeomGen jNGeomGen coe_jNGeomGen IsAffineGeomPlace jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin modularFunctionFieldBar_eq_modularFunctionFieldC exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs finrankAlong_heckeBetaBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem CharPReduction.modularRedLocHom_mem adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional"
namespace ChartGen
p2m_open "ModularCurve~jBar"

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem coeff_minpolyDiv_mem_subring (x : L) (B : Subring L) (hx : x ∈ B)
    (hf : ∀ n, algebraMap K L ((minpoly K x).coeff n) ∈ B) (i : ℕ) : (minpolyDiv K x).coeff i ∈ B := by
  suffices H : ∀ j i : ℕ, (minpolyDiv K x).natDegree < i + j → (minpolyDiv K x).coeff i ∈ B from
    H ((minpolyDiv K x).natDegree + 1) i (by omega)
  intro j
  induction j with
  | zero =>
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hi)]
    exact zero_mem _
  | succ j ih =>
    intro i hi
    rw [coeff_minpolyDiv]
    exact add_mem (hf (i + 1)) (mul_mem (ih (i + 1) (by omega)) hx)

variable [Algebra.IsSeparable K L]

private theorem repr_eq_trace_mul (pb : PowerBasis K L) (h : L) (i : Fin pb.dim) :
    pb.basis.repr h i = Algebra.trace K L
      (h * ((minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative (minpoly K pb.gen)))) := by
  haveI := pb.finite
  rw [← Module.Basis.traceDual_powerBasis_eq pb i, ← Algebra.traceForm_apply,
    ← Module.Basis.traceDual_repr_apply, Module.Basis.traceDual_traceDual]

variable {O : Type*} [CommRing O] [Algebra O K] [Algebra O L] [IsScalarTower O K L]
  [IsIntegrallyClosed O] [IsFractionRing O K]

private theorem exists_algebraMap_eq_repr_of_isIntegral (pb : PowerBasis K L) (h : L)
    (hint : ∀ i : Fin pb.dim,
      IsIntegral O (h * ((minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative (minpoly K pb.gen)))))
    (i : Fin pb.dim) : ∃ y : O, algebraMap O K y = pb.basis.repr h i := by
  haveI := pb.finite
  rw [repr_eq_trace_mul]
  exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (hint i))

section Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem ord_nonneg_of_mem' (v : Place K L) {f : L} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : L) * ((π : L) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem mem_of_ord_nonneg' (v : Place K L) {f : L} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem minpoly_eq_of_monic_of_natDegree_eq {x : L} {m : Polynomial K} (hm : m.Monic) (hroot : aeval x m = 0)
    (hdeg : m.natDegree = Module.finrank K L)
    (hgen : IntermediateField.adjoin K ({x} : Set L) = ⊤) : minpoly K x = m := by
  have hint : IsIntegral K x := ⟨m, hm, by rwa [← aeval_def]⟩
  have hnat : (minpoly K x).natDegree = Module.finrank K L := by
    rw [← IntermediateField.adjoin.finrank hint, hgen, IntermediateField.finrank_top']
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hm (minpoly.dvd _ _ hroot) ?_).symm
  rw [hdeg, hnat]

private theorem exists_powerBasis_of_adjoin_eq_top {x : L} (hint : IsIntegral K x)
    (hgen : IntermediateField.adjoin K ({x} : Set L) = ⊤) :
    ∃ pb : PowerBasis K L, pb.gen = x ∧ pb.dim = (minpoly K x).natDegree :=
  ⟨(IntermediateField.adjoin.powerBasis hint).map
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv), rfl, rfl⟩

private theorem eq_sum_repr_mul_pow (pb : PowerBasis K L) {n : ℕ} (hdim : pb.dim = n) (h : L) :
    h = ∑ i : Fin n, algebraMap K L (pb.basis.repr h (Fin.cast hdim.symm i)) * pb.gen ^ (i : ℕ) := by
  conv_lhs => rw [← pb.basis.sum_repr h]
  subst hdim
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pb.basis_eq_pow, Algebra.smul_def]
  rfl

private theorem coeff_minpoly_mem_of_isIntegral {K₀ : Type*} [Field K₀] [Algebra K₀ K] (v : Place K₀ K) (x : L)
    (hx : IsIntegral v.toValuationSubring x) (i : ℕ) : (minpoly K x).coeff i ∈ v.toValuationSubring := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, coeff_map]
  exact ((minpoly v.toValuationSubring x).coeff i).2

private theorem natDegree_minpoly_of_adjoin_eq_top [FiniteDimensional K L] (x : L)
    (hx : IntermediateField.adjoin K ({x} : Set L) = ⊤) : (minpoly K x).natDegree = Module.finrank K L := by
  rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite K x), hx, IntermediateField.finrank_top']

private theorem pow_eq_sum_neg_coeff_minpoly (x : L) (hx : IsIntegral K x) {n : ℕ} (hn : (minpoly K x).natDegree = n) :
    x ^ n = ∑ i : Fin n, (-(algebraMap K L ((minpoly K x).coeff i))) * x ^ (i : ℕ) := by
  have h0 := minpoly.aeval K x
  rw [(minpoly.monic hx).as_sum, hn] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  rw [Finset.sum_range] at h0
  rw [eq_neg_of_add_eq_zero_left h0, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_mul]

end Generic
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"

section AtPlace

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']

private theorem isIntegral_of_forall_ord_fiber_nonneg (v : Place K F) {y : F'} (hy : ∀ w ∈ v.fiber F', 0 ≤ w.ord y) :
    IsIntegral v.toValuationSubring y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · exact isIntegral_zero
  obtain ⟨c, hc⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg hy0 hy
  rw [← hc]
  exact c.2

private theorem repr_mem_of_forall_ord_fiber_nonneg (v : Place K F) (pb : PowerBasis F F') (h : F')
    (hint : ∀ j : Fin pb.dim, ∀ w ∈ v.fiber F',
      0 ≤ w.ord (h * ((minpolyDiv F pb.gen).coeff j / aeval pb.gen (derivative (minpoly F pb.gen)))))
    (i : Fin pb.dim) : pb.basis.repr h i ∈ v.toValuationSubring := by
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_repr_of_isIntegral (O := v.toValuationSubring) pb h
    (fun j => isIntegral_of_forall_ord_fiber_nonneg v (hint j)) i
  rw [← hy]
  exact y.2

private theorem repr_mem_of_forall_mem_fiber (v : Place K F) (pb : PowerBasis F F') (h : F')
    (hint : ∀ j : Fin pb.dim, ∀ w ∈ v.fiber F',
      h * ((minpolyDiv F pb.gen).coeff j / aeval pb.gen (derivative (minpoly F pb.gen))) ∈ w.toValuationSubring)
    (i : Fin pb.dim) : pb.basis.repr h i ∈ v.toValuationSubring :=
  repr_mem_of_forall_ord_fiber_nonneg v pb h (fun j w hw => ord_nonneg_of_mem' w (hint j w hw)) i

end AtPlace
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"

section Modular

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

@[reducible] private noncomputable def alongAlgebra : Algebra (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) :=
  algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)

attribute [local instance] alongAlgebra

private theorem alongTower :
    IsScalarTower (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) :=
  isScalarTower_along _

attribute [local instance] alongTower

variable {N q}

private theorem algebraMap_along :
    algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) =
      (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom :=
  rfl

private theorem algebraMap_along_apply (c : modularFunctionFieldBar N) :
    algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) c =
      heckeAlphaBar (AlgebraicClosure ℚ) N q c := by
  rw [algebraMap_along, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

private theorem alpha_injective : Function.Injective (heckeAlphaBar (AlgebraicClosure ℚ) N q) := by
  rw [← AlgHom.coe_toRingHom]
  exact (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.injective

private theorem finrank_along
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1) :
    Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) = q + 1 :=
  hdeg

private theorem finiteDimensional_along
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1) :
    FiniteDimensional (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := by
  have h := finrank_along hdeg
  exact Module.finite_of_finrank_pos (by omega)

omit [NeZero N] in
private theorem charZero_bar : CharZero (modularFunctionFieldBar N) :=
  charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective

private theorem isSeparable_along
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1) :
    Algebra.IsSeparable (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := by
  haveI := finiteDimensional_along hdeg
  haveI := Algebra.IsAlgebraic.of_finite (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q))
  haveI := charZero_bar (N := N)
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

private theorem adjoin_along_eq_top (z : modularFunctionFieldBar (N * q))
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤) :
    IntermediateField.adjoin (modularFunctionFieldBar N) ({z} : Set (modularFunctionFieldBar (N * q))) = ⊤ := by
  have hle : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) ≤
        (IntermediateField.adjoin (modularFunctionFieldBar N)
          ({z} : Set (modularFunctionFieldBar (N * q)))).restrictScalars (AlgebraicClosure ℚ) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (⟨a, rfl⟩ | rfl)
    · exact (IntermediateField.mem_restrictScalars _).mpr (IntermediateField.algebraMap_mem _ a)
    · exact (IntermediateField.mem_restrictScalars _).mpr
        (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
  rw [hgen] at hle
  rw [eq_top_iff]
  intro f _
  exact (IntermediateField.mem_restrictScalars _).mp (hle IntermediateField.mem_top)

private theorem aeval_along_eq (m : Polynomial (modularFunctionFieldBar N)) (z : modularFunctionFieldBar (N * q)) :
    aeval z m = (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z := by
  rw [aeval_def, eval₂_eq_eval_map]
  rfl

private theorem exists_powerBasis_along
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤)
    (m : Polynomial (modularFunctionFieldBar N)) (hm : m.Monic) (hdegm : m.natDegree = q + 1)
    (hroot : (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0) :
    ∃ pb : PowerBasis (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)),
      pb.gen = z ∧ pb.dim = q + 1 ∧ minpoly (modularFunctionFieldBar N) z = m := by
  have hgen' := adjoin_along_eq_top z hgen
  have haeval : aeval z m = 0 := by rw [aeval_along_eq]; exact hroot
  have hfin := finrank_along hdeg
  have hmin : minpoly (modularFunctionFieldBar N) z = m :=
    minpoly_eq_of_monic_of_natDegree_eq hm haeval (by rw [hdegm, hfin]) hgen'
  have hint : IsIntegral (modularFunctionFieldBar N) z := ⟨m, hm, by rwa [← aeval_def]⟩
  obtain ⟨pb, hpb, hdim⟩ := exists_powerBasis_of_adjoin_eq_top hint hgen'
  exact ⟨pb, hpb, by rw [hdim, hmin, hdegm], hmin⟩

private theorem adjoin_union_eq_top_of_linearIndependent
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hli : LinearIndependent (modularFunctionFieldBar N) fun i : Fin (q + 1) => z ^ (i : ℕ)) :
    IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤ := by
  haveI := finiteDimensional_along hdeg
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, finrank_along hdeg])
  rw [eq_top_iff]
  intro f _
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (modularFunctionFieldBar N)).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span (modularFunctionFieldBar N)
      (Set.range fun i : Fin (q + 1) => z ^ (i : ℕ)))
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, algebraMap_along_apply]
  have hz : z ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) :=
    IntermediateField.subset_adjoin _ _ (Or.inr rfl)
  have hc : heckeAlphaBar (AlgebraicClosure ℚ) N q (c i) ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) :=
    IntermediateField.subset_adjoin _ _ (Or.inl ⟨c i, rfl⟩)
  exact mul_mem hc (pow_mem hz _)

private theorem exists_monic_data_of_linearIndependent
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hli : LinearIndependent (modularFunctionFieldBar N) fun i : Fin (q + 1) => z ^ (i : ℕ)) :
    IntermediateField.adjoin (AlgebraicClosure ℚ)
        (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤ ∧
      ∃ m : Polynomial (modularFunctionFieldBar N), m.Monic ∧ m.natDegree = q + 1 ∧
        (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0 ∧
        z ^ (q + 1) =
          ∑ i : Fin (q + 1), (-(heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i))) * z ^ (i : ℕ) := by
  haveI := finiteDimensional_along hdeg
  have hgen := adjoin_union_eq_top_of_linearIndependent hdeg z hli
  have hint : IsIntegral (modularFunctionFieldBar N) z := IsIntegral.of_finite (modularFunctionFieldBar N) z
  have hnat : (minpoly (modularFunctionFieldBar N) z).natDegree = q + 1 := by
    rw [natDegree_minpoly_of_adjoin_eq_top z (adjoin_along_eq_top z hgen), finrank_along hdeg]
  refine ⟨hgen, minpoly (modularFunctionFieldBar N) z, minpoly.monic hint, hnat, ?_, ?_⟩
  · rw [← aeval_along_eq]
    exact minpoly.aeval _ _
  · have h := pow_eq_sum_neg_coeff_minpoly z hint hnat
    simp only [algebraMap_along_apply] at h
    exact h

private theorem coeff_mem_of_forall_mem (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤)
    (m : Polynomial (modularFunctionFieldBar N)) (hm : m.Monic) (hdegm : m.natDegree = q + 1)
    (hroot : (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hz : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = u₀ → z ∈ W.toValuationSubring)
    (i : ℕ) : m.coeff i ∈ u₀.toValuationSubring := by
  haveI := finiteDimensional_along hdeg
  haveI := isSeparable_along hdeg
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨-, -, -, hmin⟩ := exists_powerBasis_along hdeg z hgen m hm hdegm hroot
  rw [← hmin]
  refine coeff_minpoly_mem_of_isIntegral u₀ z (isIntegral_of_forall_ord_fiber_nonneg u₀ fun W hW => ?_) i
  exact ord_nonneg_of_mem' W (hz W (Place.mem_fiber.mp hW))

private theorem coeff_mem_of_forall_mem_affine (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤)
    (m : Polynomial (modularFunctionFieldBar N)) (hm : m.Monic) (hdegm : m.natDegree = q + 1)
    (hroot : (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0)
    (hzreg : ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      CharPModel.jBar N ∈ u₀.toValuationSubring →
      ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = u₀ → z ∈ W.toValuationSubring) :
    ∀ i : ℕ, ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      CharPModel.jBar N ∈ u₀.toValuationSubring → m.coeff i ∈ u₀.toValuationSubring :=
  fun i u₀ hu₀ => coeff_mem_of_forall_mem hα hdeg z hgen m hm hdegm hroot u₀ (hzreg u₀ hu₀) i

end Modular
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"

end ModularCurve.ChartGen
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve ModularCurve.CharPModel ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.PlaceSpecialization"

private theorem aff_FIN
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k) (fm : FibreModel N A ℓ k red)
    (v : Place k (modularFunctionFieldC k N))
    (hv : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring) :
    (∀ b : fm.BFin, fm.piFin b ∈ v.toValuationSubring) ∧
      ∀ g : modularFunctionFieldC k N, g ∈ v.toValuationSubring →
        ∃ b b' : fm.BFin, ¬ v.HasValue (fm.piFin b') (0 : k) ∧ g * fm.piFin b' = fm.piFin b :=
  ModularCurve.CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem N A ℓ hℓN k red fm v hv

private theorem aff_GLN
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hqN : ¬ q ∣ N) :
    ∀ t : modularFunctionFieldBar N,
      (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red →
      (∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        CharPModel.jBar N ∈ u₀.toValuationSubring → t ∈ u₀.toValuationSubring) →
      ∃ p : Polynomial (CharPModel.affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (CharPModel.affineBaseFin N A).subtype t p = 0 :=
  ModularCurve.CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem red hqN

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff charP_modularFunctionFieldC frobOnPlacesGeomLevel_surjective KroneckerCongruence jGeomGen jNGeomGen coe_jNGeomGen IsAffineGeomPlace jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin modularFunctionFieldBar_eq_modularFunctionFieldC exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs finrankAlong_heckeBetaBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem CharPReduction.modularRedLocHom_mem adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ChartEtaleAt IsChartAt ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j d0_j_pole d1"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private noncomputable def aff_gens (fm : FibreModel N A q k red) : Set (modularFunctionFieldBar (N * q)) :=
  Set.range (fun b : fm.BFin =>
      heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    ∪ Set.range (fun b : fm.BFin =>
      heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))

private noncomputable def aff_ring (fm : FibreModel N A q k red) : Subring (modularFunctionFieldBar (N * q)) :=
  Subring.closure (aff_gens fm)

private noncomputable def aff_S (fm : FibreModel N A q k red) : Set (modularFunctionFieldBar (N * q)) :=
  (aff_ring fm : Set (modularFunctionFieldBar (N * q)))

private theorem aff_mem_S_iff (fm : FibreModel N A q k red) {s : modularFunctionFieldBar (N * q)} :
    s ∈ aff_S fm ↔ s ∈ aff_ring fm := Iff.rfl

private def aff_Good (v : Place k (modularFunctionFieldC k N)) (s : modularFunctionFieldBar (N * q)) : Prop :=
  ∃ h : s ∈ R.R₁.integers,
    (R.residue₁ ⟨s, h⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring ∧
    (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst W → P.reduceFst W = v →
        ∃ a : A, W.HasValue s (a : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨s, h⟩) (red a)) ∧
    (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = v → s ∈ W.toValuationSubring)

omit [Fact (Nat.Prime q)] [CharP k q] in

private theorem plv_hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x y : F} {a b : K} (hx : w.HasValue x a) (hy : w.HasValue y b) : w.HasValue (x + y) (a + b) := by
  obtain ⟨hxm, hxr⟩ := hx
  obtain ⟨hym, hyr⟩ := hy
  refine ⟨add_mem hxm hym, ?_⟩
  have e : (⟨x + y, add_mem hxm hym⟩ : w.toValuationSubring) = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
  rw [e, map_add, hxr, hyr, map_add]

omit [Fact (Nat.Prime q)] [CharP k q] in

private theorem plv_hasValue_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x : F} {a : K} (hx : w.HasValue x a) : w.HasValue (-x) (-a) := by
  obtain ⟨hxm, hxr⟩ := hx
  refine ⟨neg_mem hxm, ?_⟩
  have e : (⟨-x, neg_mem hxm⟩ : w.toValuationSubring) = -⟨x, hxm⟩ := rfl
  rw [e, map_neg, hxr, map_neg]

section ValueSteps

variable {v : Place k (modularFunctionFieldC k N)}

variable {Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}

private theorem plv_valued_zero (h0 : (0 : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers) :
    ∃ c : A, Q.HasValue (0 : modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨0, h0⟩) (red c) := by
  refine ⟨0, ?_, ?_⟩
  · rw [ZeroMemClass.coe_zero]
    have h := Q.hasValue_algebraMap (0 : AlgebraicClosure ℚ)
    rwa [map_zero] at h
  · have e : R.residue₁ ⟨0, h0⟩ = 0 := map_zero R.residue₁
    rw [e, map_zero]
    have h := v.hasValue_algebraMap (0 : k)
    rwa [map_zero] at h

private theorem plv_valued_one (h1 : (1 : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers) :
    ∃ c : A, Q.HasValue (1 : modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨1, h1⟩) (red c) := by
  refine ⟨1, ?_, ?_⟩
  · rw [OneMemClass.coe_one]
    exact Q.hasValue_one
  · have e : R.residue₁ ⟨1, h1⟩ = 1 := map_one R.residue₁
    rw [e, map_one]
    exact v.hasValue_one

private theorem plv_valued_add {x y : modularFunctionFieldBar (N * q)} (hxI : x ∈ R.R₁.integers)
    (hyI : y ∈ R.R₁.integers)
    (hx : ∃ c : A, Q.HasValue x (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨x, hxI⟩) (red c))
    (hy : ∃ c : A, Q.HasValue y (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨y, hyI⟩) (red c)) :
    ∃ c : A, Q.HasValue (x + y) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨x + y, add_mem hxI hyI⟩) (red c) := by
  obtain ⟨c₁, hc₁, hc₁'⟩ := hx
  obtain ⟨c₂, hc₂, hc₂'⟩ := hy
  refine ⟨c₁ + c₂, ?_, ?_⟩
  · have hcoe : ((c₁ + c₂ : A) : AlgebraicClosure ℚ) = (c₁ : AlgebraicClosure ℚ) + c₂ := rfl
    rw [hcoe]
    exact plv_hasValue_add Q hc₁ hc₂
  · have e : R.residue₁ ⟨x + y, add_mem hxI hyI⟩ = R.residue₁ ⟨x, hxI⟩ + R.residue₁ ⟨y, hyI⟩ :=
      map_add R.residue₁ ⟨x, hxI⟩ ⟨y, hyI⟩
    rw [e, map_add]
    exact plv_hasValue_add v hc₁' hc₂'

private theorem plv_valued_neg {x : modularFunctionFieldBar (N * q)} (hxI : x ∈ R.R₁.integers)
    (hx : ∃ c : A, Q.HasValue x (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨x, hxI⟩) (red c)) :
    ∃ c : A, Q.HasValue (-x) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨-x, neg_mem hxI⟩) (red c) := by
  obtain ⟨c, hc, hc'⟩ := hx
  refine ⟨-c, ?_, ?_⟩
  · have hcoe : ((-c : A) : AlgebraicClosure ℚ) = -(c : AlgebraicClosure ℚ) := rfl
    rw [hcoe]
    exact plv_hasValue_neg Q hc
  · have e : R.residue₁ ⟨-x, neg_mem hxI⟩ = -R.residue₁ ⟨x, hxI⟩ := map_neg R.residue₁ ⟨x, hxI⟩
    rw [e, map_neg]
    exact plv_hasValue_neg v hc'

private theorem plv_valued_mul {x y : modularFunctionFieldBar (N * q)} (hxI : x ∈ R.R₁.integers)
    (hyI : y ∈ R.R₁.integers)
    (hx : ∃ c : A, Q.HasValue x (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨x, hxI⟩) (red c))
    (hy : ∃ c : A, Q.HasValue y (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨y, hyI⟩) (red c)) :
    ∃ c : A, Q.HasValue (x * y) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨x * y, mul_mem hxI hyI⟩) (red c) := by
  obtain ⟨c₁, hc₁, hc₁'⟩ := hx
  obtain ⟨c₂, hc₂, hc₂'⟩ := hy
  refine ⟨c₁ * c₂, ?_, ?_⟩
  · have hcoe : ((c₁ * c₂ : A) : AlgebraicClosure ℚ) = (c₁ : AlgebraicClosure ℚ) * c₂ := rfl
    rw [hcoe]
    exact hc₁.mul hc₂
  · have e : R.residue₁ ⟨x * y, mul_mem hxI hyI⟩ = R.residue₁ ⟨x, hxI⟩ * R.residue₁ ⟨y, hyI⟩ :=
        R.residue₁.map_mul ⟨x, hxI⟩ ⟨y, hyI⟩
    rw [e, map_mul]
    exact hc₁'.mul hc₂'

end ValueSteps
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"

private theorem aff_good_zero (v : Place k (modularFunctionFieldC k N)) : aff_Good R v 0 := by
  refine ⟨zero_mem _, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨0, zero_mem _⟩ = 0 := map_zero R.residue₁
    rw [e]
    exact zero_mem _
  · intro W _ _
    exact plv_valued_zero R (zero_mem _)
  · intro W _
    exact zero_mem _

private theorem aff_good_one (v : Place k (modularFunctionFieldC k N)) : aff_Good R v 1 := by
  refine ⟨one_mem _, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨1, one_mem _⟩ = 1 := map_one R.residue₁
    rw [e]
    exact one_mem _
  · intro W _ _
    exact plv_valued_one R (one_mem _)
  · intro W _
    exact one_mem _

private theorem aff_good_add (v : Place k (modularFunctionFieldC k N)) {s t : modularFunctionFieldBar (N * q)}
    (hs : aff_Good R v s) (ht : aff_Good R v t) : aff_Good R v (s + t) := by
  obtain ⟨hsI, hsr, hsv, hso⟩ := hs
  obtain ⟨htI, htr, htv, hto⟩ := ht
  refine ⟨add_mem hsI htI, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨s + t, add_mem hsI htI⟩ = R.residue₁ ⟨s, hsI⟩ + R.residue₁ ⟨t, htI⟩ :=
      map_add R.residue₁ ⟨s, hsI⟩ ⟨t, htI⟩
    rw [e]
    exact add_mem hsr htr
  · intro W hW hWv
    exact plv_valued_add R hsI htI (hsv W hW hWv) (htv W hW hWv)
  · intro W hW
    exact add_mem (hso W hW) (hto W hW)

private theorem aff_good_neg (v : Place k (modularFunctionFieldC k N)) {s : modularFunctionFieldBar (N * q)}
    (hs : aff_Good R v s) : aff_Good R v (-s) := by
  obtain ⟨hsI, hsr, hsv, hso⟩ := hs
  refine ⟨neg_mem hsI, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨-s, neg_mem hsI⟩ = -R.residue₁ ⟨s, hsI⟩ := map_neg R.residue₁ ⟨s, hsI⟩
    rw [e]
    exact neg_mem hsr
  · intro W hW hWv
    exact plv_valued_neg R hsI (hsv W hW hWv)
  · intro W hW
    exact neg_mem (hso W hW)

private theorem aff_good_mul (v : Place k (modularFunctionFieldC k N)) {s t : modularFunctionFieldBar (N * q)}
    (hs : aff_Good R v s) (ht : aff_Good R v t) : aff_Good R v (s * t) := by
  obtain ⟨hsI, hsr, hsv, hso⟩ := hs
  obtain ⟨htI, htr, htv, hto⟩ := ht
  refine ⟨mul_mem hsI htI, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨s * t, mul_mem hsI htI⟩ = R.residue₁ ⟨s, hsI⟩ * R.residue₁ ⟨t, htI⟩ :=
        R.residue₁.map_mul ⟨s, hsI⟩ ⟨t, htI⟩
    rw [e]
    exact mul_mem hsr htr
  · intro W hW hWv
    exact plv_valued_mul R hsI htI (hsv W hW hWv) (htv W hW hWv)
  · intro W hW
    exact mul_mem (hso W hW) (hto W hW)

private def aff_goodSubring (v : Place k (modularFunctionFieldC k N)) : Subring (modularFunctionFieldBar (N * q)) where
  carrier := {s | aff_Good R v s}
  zero_mem' := aff_good_zero R v
  one_mem' := aff_good_one R v
  add_mem' := aff_good_add R v
  neg_mem' := aff_good_neg R v
  mul_mem' := aff_good_mul R v

private theorem aff_alpha_mem (fm : FibreModel N A q k red) (b : fm.BFin) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ aff_S fm :=
  Subring.subset_closure (Or.inl ⟨b, rfl⟩)

private theorem aff_beta_mem (fm : FibreModel N A q k red) (b : fm.BFin) :
    heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ aff_S fm :=
  Subring.subset_closure (Or.inr ⟨b, rfl⟩)

private theorem aff_const_mem (fm : FibreModel N A q k red) (a : A) :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ aff_S fm := by
  have hconst := aff_alpha_mem fm ⟨CharPModel.constantsHom N A a, fm.constFin_mem a⟩
  have hcomm : heckeAlphaBar (AlgebraicClosure ℚ) N q
      (CharPModel.constantsHom N A a : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    exact (heckeAlphaBar (AlgebraicClosure ℚ) N q).commutes (a : AlgebraicClosure ℚ)
  rw [hcomm] at hconst
  exact hconst

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.AlgebraicCurve.Place.ord_nonneg_of_mem_pn" "AlgebraicCurve.Place.ord_nonneg_of_mem_pn"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.AlgebraicCurve.Place.mem_of_ord_nonneg_pn" "AlgebraicCurve.Place.mem_of_ord_nonneg_pn"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.AlgebraicCurve.Place.ord_algebraMap_pn" "AlgebraicCurve.Place.ord_algebraMap_pn"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn" "AlgebraicCurve.Place.ne_zero_of_ord_pos_pn"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn" "AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm
  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => not_isUnit_zero⟩
  · rw [v.isUnit_iff_ord_eq_zero_pn hsub h0]
    have hnn := v.ord_nonneg_of_mem_pn hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {g : F} {c : K} (h : 0 < v.ord (g - algebraMap K F c)) :
    v.HasValue g c := by
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring :=
    v.mem_of_ord_nonneg_pn (v.ne_zero_of_ord_pos_pn h) h.le
  have hg : g ∈ v.toValuationSubring := by
    have h' := add_mem hsub (v.algebraMap_mem' c)
    rwa [sub_add_cancel] at h'
  exact (v.hasValue_iff_eq_or_ord_sub_pos_pn hg c).mpr (Or.inr h)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn"
private theorem pnN_coe_algebraMap {L : Type*} [Field L] (E : IntermediateField L (LaurentSeries L))
    (x : L) : ((algebraMap L E x : E) : LaurentSeries L) = algebraMap L (LaurentSeries L) x := by
  rw [IsScalarTower.algebraMap_apply L E (LaurentSeries L) x]
  rfl

private theorem pnN_const_mem (a : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) :
        modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized N A.toSubring red := by
  rw [pnN_coe_algebraMap]
  exact CharPReduction.subring_le_localizedAtKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
    (CharPReduction.constSeries_mem_modularRing N A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩)

private noncomputable def packA_g (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : CharPReduction.integralCoeffs A.toSubring) : LaurentSeries A where
  coeff n := ⟨(x : LaurentSeries (AlgebraicClosure ℚ)).coeff n, x.2 n⟩
  isPWO_support' := (x : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support.mono
    (fun _ hn h => hn (Subtype.ext h))

private theorem coeffMap_subtype_packA_g (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : CharPReduction.integralCoeffs A.toSubring) :
    coeffMap A.subtype (packA_g A x) = (x : LaurentSeries (AlgebraicClosure ℚ)) := by
  ext n
  rfl

private theorem coeffMap_residue_packA_g (A : ValuationSubring (AlgebraicClosure ℚ)) (red : A →+* k)
    (x : CharPReduction.integralCoeffs A.toSubring) :
    coeffMap red (packA_g A x) = CharPReduction.coeffRed A.toSubring red x := by
  ext n
  rw [coeffMap_coeff, CharPReduction.coeffRed_coeff]
  rfl

private theorem coeffEmb_qExpand_aux (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n x)
      = qExpand (AlgebraicClosure ℚ) n (coeffEmb (AlgebraicClosure ℚ) x) := by
  ext m
  by_cases hm : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := hm
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hm, qExpand_coeff_of_not_dvd n _ hm, map_zero]

private theorem aff_residue_surjective [IsAlgClosed k] (v : Place k (modularFunctionFieldC k N)) :
    Function.Surjective (algebraMap k v.ResidueField) := by
  have h1 : Module.finrank k v.ResidueField = 1 := place_deg_eq_one_of_isAlgClosed k N v
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp h1 x
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

private theorem aff_exists_j_value (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a₀ : A, 0 < w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a₀ : AlgebraicClosure ℚ)) := by
  by_contra hcon
  have hle : ∀ a : A, w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ)) ≤ 0 :=
    fun a => not_lt.mp (fun h => hcon ⟨a, h⟩)
  have hpole := P.d0_j_pole w hle
  rw [hw] at hpole
  have hnn : (0 : ℤ) ≤ v.ord (jGeomGen k N) := v.ord_nonneg_of_mem_pn hv1
  exact absurd hnn (not_le.mpr hpole)

private theorem aff_sub_mem_nonunits_of_hasValue {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : u.HasValue g c) :
    g - algebraMap K F c ∈ u.toValuationSubring.nonunits := by
  have hmem : g - algebraMap K F c ∈ u.toValuationSubring := sub_mem h.mem (u.algebraMap_mem' c)
  have hres : IsLocalRing.residue u.toValuationSubring ⟨g - algebraMap K F c, hmem⟩ = 0 := by
    have e : (⟨g - algebraMap K F c, hmem⟩ : u.toValuationSubring)
        = ⟨g, h.mem⟩ - algebraMap K u.toValuationSubring c := rfl
    rw [e, map_sub, h.residue_eq, u.residue_algebraMap, sub_self]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hres)

private theorem aff_hasValue_of_sub_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : g - algebraMap K F c ∈ u.toValuationSubring.nonunits) :
    u.HasValue g c := by
  by_cases hgc : g = algebraMap K F c
  · rw [hgc]
    exact u.hasValue_algebraMap c
  · have hne : g - algebraMap K F c ≠ 0 := sub_ne_zero.mpr hgc
    obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
    exact u.hasValue_of_ord_sub_pos_pn ((u.mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax)

private theorem aff_red_eq_zero_of_mem_maximalIdeal (hred : Function.Surjective red) {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  rw [← RingHom.mem_ker, hker]
  exact ha

private theorem aff_not_hasValue_zero_of_ne {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (hc : c ≠ 0) : ¬ u.HasValue g 0 :=
  fun h0 => hc (h.unique h0)

private theorem aff_frob_mem_nonunits (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N}
    (hx : x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.nonunits) :
    frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring.nonunits := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨zero_mem _, Ideal.zero_mem _⟩
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  have hord : 0 < (frobOnPlacesGeomLevel k N data hKr u).ord x :=
    ((frobOnPlacesGeomLevel k N data hKr u).mem_maximalIdeal_iff_ord_pos hx0 hmem).mp hmax

  have hinv : x⁻¹ ∉ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := by
    intro hmem'
    have h1 := (frobOnPlacesGeomLevel k N data hKr u).ord_nonneg_of_mem_pn hmem'
    rw [Place.ord_inv] at h1
    omega
  rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀] at hinv

  have hFx0 : frobeniusGeomLevel k N data hKr x ≠ 0 := by
    intro h0
    apply hinv
    rw [h0, inv_zero]
    exact zero_mem _
  have hFmem : frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring :=
    (u.toValuationSubring.mem_or_inv_mem _).resolve_right hinv
  have hFord : 0 < u.ord (frobeniusGeomLevel k N data hKr x) := by
    by_contra hle
    apply hinv
    apply u.mem_of_ord_nonneg_pn (inv_ne_zero hFx0)
    rw [Place.ord_inv]
    omega
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨hFmem, (u.mem_maximalIdeal_iff_ord_pos hFx0 hFmem).mpr hFord⟩

private theorem aff_mem_nonunits_frob_of (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N}
    (hx : frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring.nonunits) :
    x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.nonunits := by
  by_cases hx0 : x = 0
  · rw [hx0]
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨zero_mem _, Ideal.zero_mem _⟩
  have hFx0 : frobeniusGeomLevel k N data hKr x ≠ 0 := (map_ne_zero _).mpr hx0
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  have hord : 0 < u.ord (frobeniusGeomLevel k N data hKr x) := (u.mem_maximalIdeal_iff_ord_pos hFx0 hmem).mp hmax

  have hinv : x⁻¹ ∉ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := by
    rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀]
    intro hmem'
    have h1 := u.ord_nonneg_of_mem_pn hmem'
    rw [Place.ord_inv] at h1
    omega
  have hxmem : x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring :=
    ((frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.mem_or_inv_mem x).resolve_right hinv
  have hxord : 0 < (frobOnPlacesGeomLevel k N data hKr u).ord x := by
    by_contra hle
    apply hinv
    apply (frobOnPlacesGeomLevel k N data hKr u).mem_of_ord_nonneg_pn (inv_ne_zero hx0)
    rw [Place.ord_inv]
    omega
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨hxmem, ((frobOnPlacesGeomLevel k N data hKr u).mem_maximalIdeal_iff_ord_pos hx0 hxmem).mpr hxord⟩

private theorem aff_isAffine_of_isAffine_frob (u : Place k (modularFunctionFieldC k N))
    (h : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u)) : IsAffineGeomPlace k N u := by
  obtain ⟨hj, hjN⟩ := h
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  refine ⟨?_, ?_⟩
  · have h1 : jGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := hj
    rw [mem_frobOnPlacesGeomLevel_iff] at h1
    have h2 : frobeniusGeomLevel k N data hKr (jGeomGen k N) = jGeomGen k N ^ q := frobeniusGeomLevel_jq k N data hKr
    rw [h2] at h1
    exact u.toValuationSubring.mem_of_pow_mem' hq h1
  · have h1 : jNGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := hjN
    rw [mem_frobOnPlacesGeomLevel_iff] at h1
    have h2 : frobeniusGeomLevel k N data hKr (jNGeomGen k N) = jNGeomGen k N ^ q := frobeniusGeomLevel_jqN k N data hKr
    rw [h2] at h1
    exact u.toValuationSubring.mem_of_pow_mem' hq h1

private theorem aff_isAffine_frob_of_isAffine (u : Place k (modularFunctionFieldC k N))
    (h : IsAffineGeomPlace k N u) : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u) := by
  obtain ⟨hj, hjN⟩ := h
  refine ⟨?_, ?_⟩
  · show jGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring
    rw [mem_frobOnPlacesGeomLevel_iff]
    have h2 : frobeniusGeomLevel k N data hKr (jGeomGen k N) = jGeomGen k N ^ q := frobeniusGeomLevel_jq k N data hKr
    rw [h2]
    exact pow_mem hj q
  · show jNGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring
    rw [mem_frobOnPlacesGeomLevel_iff]
    have h2 : frobeniusGeomLevel k N data hKr (jNGeomGen k N) = jNGeomGen k N ^ q := frobeniusGeomLevel_jqN k N data hKr
    rw [h2]
    exact pow_mem hjN q

private theorem aff_reduceSnd_affine (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    IsAffineGeomPlace k N (P.reduceSnd W) := by
  rcases P.d1 W with h | h
  · have h₁ : P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := h
    rw [hW] at h₁
    refine aff_isAffine_of_isAffine_frob (data := data) (hKr := hKr) _ ?_
    rw [← h₁]
    exact hvaff
  · have h₁ : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := h
    rw [hW] at h₁
    rw [← h₁]
    exact aff_isAffine_frob_of_isAffine v hvaff

omit [Fact q.Prime] [NeZero N] in

private theorem aff_ramificationIndexAlong_pos' (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    0 < Place.ramificationIndexAlong φ W := by
  unfold Place.ramificationIndexAlong
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact W.ramificationIndex_pos (F := laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))

omit [Fact q.Prime] [NeZero N] in

private theorem aff_hasValue_of_restrictAlong
    (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)} {c : AlgebraicClosure ℚ}
    (h : (W.restrictAlong φ hφ).HasValue x c) : W.HasValue (φ x) c := by
  by_cases hxc : x = algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c
  · rw [hxc, φ.commutes]
    exact W.hasValue_algebraMap c
  · have hne : x - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c ≠ 0 :=
      sub_ne_zero.mpr hxc
    have hmem : x - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c
        ∈ (W.restrictAlong φ hφ).toValuationSubring :=
      sub_mem h.mem ((W.restrictAlong φ hφ).algebraMap_mem' c)
    have hmax : (⟨_, hmem⟩ : (W.restrictAlong φ hφ).toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      ValuationSubring.coe_mem_nonunits_iff.mp (aff_sub_mem_nonunits_of_hasValue _ h)
    have hord := ((W.restrictAlong φ hφ).mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax
    apply W.hasValue_of_ord_sub_pos_pn
    rw [← φ.commutes, ← map_sub, W.ord_restrictAlong φ hφ]
    exact mul_pos (by exact_mod_cast aff_ramificationIndexAlong_pos' φ hφ W) hord

private theorem aff_hasValue_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (n : ℕ) : u.HasValue (g ^ n) (c ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact u.hasValue_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

private theorem aff_mem_nonunits_of_pow_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {n : ℕ} (hn : n ≠ 0) (h : g ^ n ∈ u.toValuationSubring.nonunits) : g ∈ u.toValuationSubring.nonunits := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
  have hg : g ∈ u.toValuationSubring := u.toValuationSubring.mem_of_pow_mem' hn hmem
  have hpow : (⟨g ^ n, hmem⟩ : u.toValuationSubring) = (⟨g, hg⟩ : u.toValuationSubring) ^ n := by
    apply Subtype.ext
    simp
  rw [hpow] at hmax
  exact ValuationSubring.coe_mem_nonunits_iff.mpr
    ((IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_of_pow_mem n hmax)

private theorem aff_hasValue_frob_apply (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N} {t : k}
    (h : (frobOnPlacesGeomLevel k N data hKr u).HasValue x t) : u.HasValue (frobeniusGeomLevel k N data hKr x) t := by
  have h1 := aff_frob_mem_nonunits u (aff_sub_mem_nonunits_of_hasValue _ h)
  rw [map_sub, AlgHom.commutes] at h1
  exact aff_hasValue_of_sub_mem_nonunits u h1

private theorem aff_hasValue_frobOnPlaces (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N} {t : k}
    (h : u.HasValue (frobeniusGeomLevel k N data hKr x) t) : (frobOnPlacesGeomLevel k N data hKr u).HasValue x t := by
  have h1 := aff_sub_mem_nonunits_of_hasValue u h
  rw [← AlgHom.commutes (frobeniusGeomLevel k N data hKr) t, ← map_sub] at h1
  exact aff_hasValue_of_sub_mem_nonunits _ (aff_mem_nonunits_frob_of u h1)

private theorem aff_redBar_comp_residue : R.redBar.comp (IsLocalRing.residue A) = red :=
  RingHom.ext fun a => R.redBar_residue a

private theorem aff_good_residue_of_coe_eq (g : modularFunctionFieldBar (N * q)) (y : LaurentSeries A)
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y) :
    ∃ h : g ∈ R.R₁.integers, ((R.residue₁ ⟨g, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red y := by
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := hg ▸ g.2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hy
  have hgeq : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) = g := Subtype.ext hg.symm
  have key : ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers,
      ((R.residue₁ ⟨_, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red y := by
    refine ⟨h, ?_⟩
    rw [R.residue₁_apply, R.ι_coe, hres, coeffMap_coeffMap, aff_redBar_comp_residue]
  exact hgeq ▸ key

private theorem aff_bfin_coe_mem_integralCoeffs (fm : FibreModel N A q k red) (b : fm.BFin) :
    ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.integralCoeffs A.toSubring :=
  mem_integralCoeffs_of_integral_affineBaseFin A N _ (fm.integralFin b)

private theorem aff_residue_alpha (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = fm.piFin b := by
  have hint := aff_bfin_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (packA_g A ⟨_, hint⟩) := by
    rw [coe_heckeAlphaBar, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := aff_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_residue_packA_g, FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hint]

private theorem aff_residue_beta (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (fm.piFin b) := by
  have hint := aff_bfin_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffMap A.subtype (qExpand A q (packA_g A ⟨_, hint⟩)) := by
    rw [coe_heckeBetaBar, coeffMap_qExpand, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := aff_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_qExpand, coeffMap_residue_packA_g, frobeniusGeomLevel_apply_coe,
    FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hint]

private theorem aff_residue_const (a : A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = algebraMap k (modularFunctionFieldC k N) (red a) := by
  have hcoe : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (HahnSeries.single 0 a) := by
    rw [pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single, coeffMap_single]
    first
      | done
      | rfl
  obtain ⟨h, hres⟩ := aff_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext ?_⟩
  rw [hres, coeffMap_single, pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single]

private theorem aff_bfin_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring) (b : fm.BFin)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a : A, w.HasValue (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piFin b) (red a) := by
  obtain ⟨a₀, ha₀⟩ := aff_exists_j_value v hv1 _ hw

  have hreg : fm.piFin b ∈ v.toValuationSubring := (aff_FIN N A q hqN k red fm v hv1).1 b
  obtain ⟨c, hc, -⟩ := v.exists_hasValue_of_surjective (aff_residue_surjective v) hreg
  obtain ⟨a₁, rfl⟩ := hred c

  set b₁ : fm.BFin := b - ⟨CharPModel.constantsHom N A a₁, fm.constFin_mem a₁⟩ with hb₁
  have hpi : (fm.piFin b₁ : modularFunctionFieldC k N)
      = fm.piFin b - algebraMap k (modularFunctionFieldC k N) (red a₁) := by
    rw [hb₁, map_sub, fm.piFin_const]
  have hnu : (fm.piFin b₁ : modularFunctionFieldC k N) ∈ v.toValuationSubring.nonunits := by
    rw [hpi]
    exact aff_sub_mem_nonunits_of_hasValue v hc
  have hsp : fm.spPlace hred dataAll hsep w = v := by
    rw [← hP]
    exact hw
  rw [← hsp] at hnu
  obtain ⟨a₂, ha₂m, ha₂⟩ := (fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep _ a₀ ha₀ b₁).mp hnu

  have hdiff : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
      = (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
            (a₂ : AlgebraicClosure ℚ) := by
    have hcoe : ((a₁ + a₂ : A) : AlgebraicClosure ℚ) = (a₁ : AlgebraicClosure ℚ) + a₂ := rfl
    have hb₁' : (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
              (a₁ : AlgebraicClosure ℚ) := by
      rw [hb₁]
      push_cast
      rfl
    rw [hcoe, hb₁', map_add, sub_sub]
  have ha₂' : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
        ∈ w.toValuationSubring.nonunits := by
    rw [hdiff]
    exact ha₂
  have hval_w : w.HasValue
      (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ((a₁ + a₂ : A) : AlgebraicClosure ℚ) :=
    aff_hasValue_of_sub_mem_nonunits _ ha₂'
  refine ⟨a₁ + a₂, hval_w, ?_⟩

  rw [map_add, aff_red_eq_zero_of_mem_maximalIdeal hred ha₂m, add_zero]
  exact hc

private theorem aff_alpha_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    ∃ a : A, W.HasValue (heckeAlphaBar (AlgebraicClosure ℚ) N q
        (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piFin b) (red a) := by
  obtain ⟨a, haw, hav⟩ := aff_bfin_values fm hred dataAll hsep hP hqN v hvaff.1 b
    (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) hW
  exact ⟨a, aff_hasValue_of_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W haw, hav⟩

private theorem aff_beta_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    ∃ a : A, W.HasValue (heckeBetaBar (AlgebraicClosure ℚ) N q
        (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) (a : AlgebraicClosure ℚ) ∧
      (P.reduceSnd W).HasValue (fm.piFin b) (red a) := by
  obtain ⟨a, haw, hau⟩ := aff_bfin_values fm hred dataAll hsep hP hqN (P.reduceSnd W) (aff_reduceSnd_affine v hvaff W hW).1 b
    (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) rfl
  exact ⟨a, aff_hasValue_of_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ W haw, hau⟩

private theorem aff_good_alpha [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin) :
    aff_Good R v (heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) := by
  obtain ⟨hI, hres⟩ := aff_residue_alpha R fm b
  refine ⟨hI, ?_, ?_, ?_⟩
  · rw [hres]
    exact (aff_FIN N A q hqN k red fm v hvaff.1).1 b
  · intro W _ hWv
    rw [hres]
    exact aff_alpha_values fm hred dataAll hsep hP hqN v hvaff b W hWv
  · intro W hWv
    obtain ⟨a, haW, -⟩ := aff_alpha_values fm hred dataAll hsep hP hqN v hvaff b W hWv
    exact haW.mem

private theorem aff_good_beta [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin) :
    aff_Good R v (heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) := by
  obtain ⟨hI, hres⟩ := aff_residue_beta R fm b
  refine ⟨hI, ?_, ?_, ?_⟩
  · rw [hres]
    have h1 : fm.piFin b ∈ (frobOnPlacesGeomLevel k N data hKr v).toValuationSubring :=
      (aff_FIN N A q hqN k red fm _ (aff_isAffine_frob_of_isAffine v hvaff).1).1 b
    rwa [mem_frobOnPlacesGeomLevel_iff] at h1
  · intro W hWs hWv
    obtain ⟨a, haW, hau⟩ := aff_beta_values fm hred dataAll hsep hP hqN v hvaff b W hWv
    refine ⟨a, haW, ?_⟩
    rw [hres]
    have hu : P.reduceSnd W = frobOnPlacesGeomLevel k N data hKr v := by
      have h₁ : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := hWs.1
      rw [← h₁, hWv]
    rw [hu] at hau
    exact aff_hasValue_frob_apply v hau
  · intro W hWv
    obtain ⟨a, haW, -⟩ := aff_beta_values fm hred dataAll hsep hP hqN v hvaff b W hWv
    exact haW.mem

private theorem aff_good_of_mem [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v)
    {s : modularFunctionFieldBar (N * q)} (hs : s ∈ aff_S fm) : aff_Good R v s := by
  have hle : aff_ring fm ≤ aff_goodSubring R v := by
    rw [aff_ring, Subring.closure_le]
    rintro x (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact aff_good_alpha R fm hred dataAll hsep hP hqN v hvaff b
    · exact aff_good_beta R fm hred dataAll hsep hP hqN v hvaff b
  exact hle ((aff_mem_S_iff fm).mp hs)

private theorem aff_exists_separator [IsAlgClosed k] (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    (v v' : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring)
    (hv' : jGeomGen k N ∈ v'.toValuationSubring) (hne : v' ≠ v) :
    ∃ b : fm.BFin, v'.HasValue (fm.piFin b) (0 : k) ∧ ¬ v.HasValue (fm.piFin b) (0 : k) := by
  by_contra hcon
  have hall : ∀ b : fm.BFin, v'.HasValue (fm.piFin b) (0 : k) → v.HasValue (fm.piFin b) (0 : k) :=
    fun b h1 => Classical.byContradiction fun h2 => hcon ⟨b, h1, h2⟩
  apply hne
  have hle : v.toValuationSubring ≤ v'.toValuationSubring := by
    intro g hg
    obtain ⟨b, b', hb', hgb⟩ := (aff_FIN N A q hqN k red fm v hv).2 g hg
    have hb'mem : fm.piFin b' ∈ v'.toValuationSubring := (aff_FIN N A q hqN k red fm v' hv').1 b'
    obtain ⟨c, hc, -⟩ := v'.exists_hasValue_of_surjective (aff_residue_surjective v') hb'mem
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hb' (hall b' hc)
    have hg' : g = fm.piFin b * (fm.piFin b')⁻¹ := (eq_mul_inv_iff_mul_eq₀ (hc.ne_zero hc0)).mpr hgb
    rw [hg']
    exact mul_mem ((aff_FIN N A q hqN k red fm v' hv').1 b) (hc.inv hc0).mem
  exact (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle v'.ne_top')).symm

private theorem aff_separates [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v)
    (hint : ∀ s ∈ aff_S fm, s ∈ R.R₁.integers)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hWs : P.IsStrictSnd W) (hW : P.reduceFst W = v) :
    ∃ (u : modularFunctionFieldBar (N * q)) (hu : u ∈ aff_S fm),
      ¬ v.HasValue (R.residue₁ ⟨u, hint u hu⟩) (0 : k) ∧ 0 < W.ord u := by
  have hu_eq : frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) = v := by
    have h₁ : P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := hWs.1
    rw [← h₁, hW]
  have hguard : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W)) ≠ P.reduceSnd W := hWs.2
  have huaff := aff_reduceSnd_affine v hvaff W hW
  have hu2aff : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W))) :=
    aff_isAffine_frob_of_isAffine _ (aff_isAffine_frob_of_isAffine _ huaff)
  obtain ⟨b, hb2, hbu⟩ := aff_exists_separator fm hqN (P.reduceSnd W) _ huaff.1 hu2aff.1 hguard
  obtain ⟨c, hWc, huc⟩ := aff_beta_values fm hred dataAll hsep hP hqN v hvaff b W hW
  have hc0 : red c ≠ 0 := fun h0 => hbu (h0 ▸ huc)
  obtain ⟨hβI, hβres⟩ := aff_residue_beta R fm b
  obtain ⟨hcI, hcres⟩ := aff_residue_const R (N := N) (q := q) c
  have hwit : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ aff_S fm :=
    (aff_mem_S_iff fm).mpr (sub_mem ((aff_mem_S_iff fm).mp (aff_beta_mem fm b)) ((aff_mem_S_iff fm).mp (aff_const_mem fm c)))

  have hres : R.residue₁ ⟨heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), hint _ hwit⟩
      = frobeniusGeomLevel k N data hKr (fm.piFin b) - algebraMap k (modularFunctionFieldC k N) (red c) :=
    (R.residue₁.map_sub ⟨_, hβI⟩ ⟨_, hcI⟩).trans (congrArg₂ (· - ·) hβres hcres)

  have h2 : (frobOnPlacesGeomLevel k N data hKr v).HasValue (fm.piFin b) (0 : k) := by
    rw [← hu_eq]
    exact hb2
  have h3 : v.HasValue (frobeniusGeomLevel k N data hKr (fm.piFin b)) (0 : k) := aff_hasValue_frob_apply v h2
  refine ⟨_, hwit, ?_, ?_⟩
  · rw [hres]
    have h4 : v.HasValue (frobeniusGeomLevel k N data hKr (fm.piFin b) - algebraMap k (modularFunctionFieldC k N) (red c))
        ((0 : k) - red c) := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      exact plv_hasValue_add v h3 (plv_hasValue_neg v (v.hasValue_algebraMap (red c)))
    refine aff_not_hasValue_zero_of_ne v h4 ?_
    rw [zero_sub]
    exact neg_ne_zero.mpr hc0
  ·
    have hne0 : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have hg : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) := sub_eq_zero.mp h0
      have h6 : R.residue₁ ⟨_, hβI⟩ = R.residue₁ ⟨_, hcI⟩ := congrArg R.residue₁ (Subtype.ext hg)
      have h7 : frobeniusGeomLevel k N data hKr (fm.piFin b) = algebraMap k (modularFunctionFieldC k N) (red c) :=
        hβres.symm.trans (h6.trans hcres)
      have h5 : v.HasValue (frobeniusGeomLevel k N data hKr (fm.piFin b)) (red c) := by
        rw [h7]
        exact v.hasValue_algebraMap (red c)
      exact hc0 (h5.unique h3)

    have hmem : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ W.toValuationSubring := sub_mem hWc.mem (W.algebraMap_mem' _)
    have hmax : (⟨_, hmem⟩ : W.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      ValuationSubring.coe_mem_nonunits_iff.mp (aff_sub_mem_nonunits_of_hasValue W hWc)
    exact (W.mem_maximalIdeal_iff_ord_pos hne0 hmem).mp hmax

private theorem aff_dichotomy (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    P.IsStrictFst W ∨ P.IsStrictSnd W := by
  rcases P.d1 W with h | h
  · right
    have h₁ : P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := h
    have hv' : v = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := hW.symm.trans h₁
    refine ⟨h₁, fun h2 => hv ?_⟩
    rw [hv', h2]
  · left
    have h₁ : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := h
    refine ⟨h₁, ?_⟩
    rw [hW]
    exact hv

private theorem aff_bar_residue_surjective (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Function.Surjective (algebraMap (AlgebraicClosure ℚ) w.ResidueField) := by
  have key : ∀ E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)),
      E = modularFunctionFieldC (AlgebraicClosure ℚ) N →
        ∀ w' : Place (AlgebraicClosure ℚ) E, Module.finrank (AlgebraicClosure ℚ) w'.ResidueField = 1 := by
    rintro E rfl w'
    exact place_deg_eq_one_of_isAlgClosed (AlgebraicClosure ℚ) N w'
  have h1 := key (modularFunctionFieldBar N) (modularFunctionFieldBar_eq_modularFunctionFieldC N) w
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : w.ResidueField) one_ne_zero).mp h1 x
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

private theorem aff_jBar_ne_algebraMap (t : AlgebraicClosure ℚ) :
    CharPModel.jBar N ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) t := by
  intro h
  have h1 : ((CharPModel.jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1 : ℤ)
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) t : modularFunctionFieldBar N) :
          LaurentSeries (AlgebraicClosure ℚ)).coeff (-1 : ℤ) := by
    rw [h]
  have h2 : ((CharPModel.jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1 : ℤ) = 1 := by
    show (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1 : ℤ) = 1
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
  rw [h2, pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by decide)] at h1
  exact one_ne_zero h1

private theorem aff_bfin_mem_of_jBar_mem (fm : FibreModel N A q k red) (b : fm.BFin)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : CharPModel.jBar N ∈ w.toValuationSubring) :
    (b : modularFunctionFieldBar N) ∈ w.toValuationSubring := by
  refine w.mem_toValuationSubring_of_isIntegral_adjoin hw ?_
  have hle : CharPModel.affineBaseFin N A
      ≤ (Algebra.adjoin (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N))).toSubring := by
    rw [CharPModel.affineBaseFin, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · exact Subalgebra.algebraMap_mem _ (a : AlgebraicClosure ℚ)
    · exact Algebra.subset_adjoin (Set.mem_singleton _)
  obtain ⟨p, hp, hpb⟩ := fm.integralFin b
  let ι : CharPModel.affineBaseFin N A
      →+* Algebra.adjoin (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N)) :=
    (CharPModel.affineBaseFin N A).subtype.codRestrict _ (fun x => hle x.2)
  have hcomp : (algebraMap (Algebra.adjoin (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)).comp ι = (CharPModel.affineBaseFin N A).subtype :=
    RingHom.ext fun _ => rfl
  refine ⟨p.map ι, hp.map ι, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact hpb

private noncomputable def _root_.ModularCurve.PlaceSpecialization.redLoc (f : modularFunctionFieldBar N)
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red) :
    modularFunctionFieldC k N :=
  ⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩,
    CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨f, hf⟩⟩

p2m_export "ModularCurve.PlaceSpecialization" "redLoc"
private theorem coeffMap_qExpand_g {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext m
  by_cases hm : (n : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hm
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hm, qExpand_coeff_of_not_dvd n _ hm, map_zero]

private theorem coeffEmb_jq_eq_jqModC_g :
    coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  have hmap : jNumQ.map (algebraMap ℚ (AlgebraicClosure ℚ))
      = jNum.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    ext n
    simp [jNumQ, PowerSeries.coeff_map]
  rw [jq, jqModC, map_mul]
  congr 1
  · ext m
    rw [coeffEmb_coeff]
    by_cases hm : m = (-1 : ℤ) <;> simp [hm]
  · ext m
    rw [coeffEmb_coeff]
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, ← hmap,
        PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ (by omega), ofPowerSeries_coeff_of_neg _ (by omega), map_zero]

private theorem modularRing_le_bar_g (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    CharPReduction.modularRing N A.toSubring ≤ (modularFunctionFieldBar N).toSubring := by
  rw [CharPReduction.modularRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact (modularFunctionFieldBar N).algebraMap_mem _
  · rw [← coeffEmb_jq_eq_jqModC_g]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))
  · have h1 : jqNModC (AlgebraicClosure ℚ) N = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) := by
      rw [jqNModC, ← coeffEmb_jq_eq_jqModC_g, coeffEmb, coeffMap_qExpand_g]
    rw [h1]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))

private theorem integral_glue_g (x : CharPReduction.modularRing N A.toSubring) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)
        ∈ R.R₁.integers,
      ((R.residue₁ ⟨_, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) =
        CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
          (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) x := by
  set xI : CharPReduction.integralCoeffs A.toSubring :=
    ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩ with hxI
  have hy : coeffMap A.subtype (packA_g A xI) ∈ modularFunctionFieldBar (N * q) := by
    rw [coeffMap_subtype_packA_g]
    have := (heckeAlphaBar (AlgebraicClosure ℚ) N q
      (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)).2
    rwa [coe_heckeAlphaBar] at this
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (packA_g A xI) hy
  have hel : (⟨coeffMap A.subtype (packA_g A xI), hy⟩ : modularFunctionFieldBar (N * q)) =
      heckeAlphaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N) := by
    apply Subtype.ext
    rw [coe_heckeAlphaBar]
    exact coeffMap_subtype_packA_g A xI
  refine ⟨hel ▸ h, ?_⟩

  have key : ∀ (e : modularFunctionFieldBar (N * q))
      (_ : e = (⟨coeffMap A.subtype (packA_g A xI), hy⟩ : modularFunctionFieldBar (N * q)))
      (h' : e ∈ R.R₁.integers),
      ((R.R₁.residue ⟨e, h'⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap (IsLocalRing.residue A) (packA_g A xI) := by
    rintro e rfl h'
    exact hres
  have hres' := key _ hel.symm (hel ▸ h)
  show ((R.ι (R.R₁.residue ⟨_, hel ▸ h⟩) : modularFunctionFieldC k N) : LaurentSeries k) = _
  rw [R.ι_coe, hres', coeffMap_coeffMap]
  have hcomp : R.redBar.comp (IsLocalRing.residue A) = red := RingHom.ext R.redBar_residue
  rw [hcomp, coeffMap_residue_packA_g, CharPReduction.redRes_apply]

private theorem localized_mem_g (t : modularFunctionFieldBar N)
    (r s : CharPReduction.modularRing N A.toSubring)
    (hs : s ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring))
    (hts : (t : LaurentSeries (AlgebraicClosure ℚ)) * s = r) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers := by
  obtain ⟨hr₁, -⟩ := integral_glue_g (red := red) R r
  obtain ⟨hs₁, hsres⟩ := integral_glue_g (red := red) R s
  have hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) s ≠ 0 :=
    CharPReduction.redRes_ne_zero_of_notMem hs
  have hsres₀ : R.R₁.residue ⟨_, hs₁⟩ ≠ 0 := by
    intro h0
    apply hsred
    rw [← hsres]
    show ((R.ι (R.R₁.residue ⟨_, hs₁⟩) : modularFunctionFieldC k N) : LaurentSeries k) = 0
    rw [h0, map_zero]
    rfl
  obtain ⟨b, hb⟩ := (R.R₁.isUnit_of_residue_ne_zero hsres₀).exists_right_inv

  have hb' : heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨s, modularRing_le_bar_g N A s.2⟩ *
      (b : modularFunctionFieldBar (N * q)) = 1 := by
    have := congrArg (fun z : R.R₁.integers => (z : modularFunctionFieldBar (N * q))) hb
    simpa using this
  have hts' : t * (⟨s, modularRing_le_bar_g N A s.2⟩ : modularFunctionFieldBar N) =
      ⟨r, modularRing_le_bar_g N A r.2⟩ := Subtype.ext hts
  have hmul : heckeAlphaBar (AlgebraicClosure ℚ) N q t *
      heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨s, modularRing_le_bar_g N A s.2⟩ =
      heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨r, modularRing_le_bar_g N A r.2⟩ := by
    rw [← map_mul, hts']
  have ht_eq : heckeAlphaBar (AlgebraicClosure ℚ) N q t =
      heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨r, modularRing_le_bar_g N A r.2⟩ *
        (b : modularFunctionFieldBar (N * q)) := by
    calc heckeAlphaBar (AlgebraicClosure ℚ) N q t
        = heckeAlphaBar (AlgebraicClosure ℚ) N q t *
            (heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨s, modularRing_le_bar_g N A s.2⟩ *
              (b : modularFunctionFieldBar (N * q))) := by rw [hb', mul_one]
      _ = _ := by rw [← mul_assoc, hmul]
  rw [ht_eq]
  exact mul_mem hr₁ b.2

private theorem localized_res_g (t : modularFunctionFieldBar N)
    (r s : CharPReduction.modularRing N A.toSubring)
    (hs : s ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring))
    (hts : (t : LaurentSeries (AlgebraicClosure ℚ)) * s = r)
    (hmem : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) :
    R.residue₁ ⟨_, hmem⟩ = redLoc t ⟨r, s, hs, hts⟩ := by
  obtain ⟨hr₁, hrres⟩ := integral_glue_g (red := red) R r
  obtain ⟨hs₁, hsres⟩ := integral_glue_g (red := red) R s
  have hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) s ≠ 0 :=
    CharPReduction.redRes_ne_zero_of_notMem hs
  have hts' : t * (⟨s, modularRing_le_bar_g N A s.2⟩ : modularFunctionFieldBar N) =
      ⟨r, modularRing_le_bar_g N A r.2⟩ := Subtype.ext hts
  have hprod : (⟨_, hmem⟩ : R.R₁.integers) * ⟨_, hs₁⟩ = ⟨_, hr₁⟩ := by
    apply Subtype.ext
    show heckeAlphaBar (AlgebraicClosure ℚ) N q t * heckeAlphaBar (AlgebraicClosure ℚ) N q _ =
      heckeAlphaBar (AlgebraicClosure ℚ) N q _
    rw [← map_mul, hts']
  have hres_mul : R.residue₁ ⟨_, hmem⟩ * R.residue₁ ⟨_, hs₁⟩ = R.residue₁ ⟨_, hr₁⟩ := by
    rw [← map_mul, hprod]
  have hL : ((R.residue₁ ⟨_, hmem⟩ : modularFunctionFieldC k N) : LaurentSeries k) *
      CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) s =
      CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) r := by
    rw [← hsres, ← hrres, ← hres_mul]
    push_cast
    rfl
  have hR : ((redLoc t ⟨r, s, hs, hts⟩ : modularFunctionFieldC k N) : LaurentSeries k) *
      CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) s =
      CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) r := by
    have h0 := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing N A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨_, ⟨r, s, hs, hts⟩⟩ hts
    exact h0
  apply Subtype.ext
  exact mul_right_cancel₀ hsred (hL.trans hR.symm)

private theorem localized_glue_g (t : modularFunctionFieldBar N)
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = redLoc t ht := by
  obtain ⟨r, s, hs, hts⟩ := ht
  exact ⟨localized_mem_g R t r s hs hts, localized_res_g R t r s hs hts _⟩

private theorem gen_atkinLehnerBar_heckeAlphaBar (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q t) =
      heckeBetaBar (AlgebraicClosure ℚ) N q t := by
  have hex := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ).1
  exact AlgHom.congr_fun hlegs t

private theorem gen_residue_mul {x y z : modularFunctionFieldBar (N * q)} (hx : x ∈ R.R₁.integers)
    (hy : y ∈ R.R₁.integers) (hz : z ∈ R.R₁.integers) (h : x * y = z) :
    R.R₁.residue ⟨x, hx⟩ * R.R₁.residue ⟨y, hy⟩ = R.R₁.residue ⟨z, hz⟩ := by
  rw [← map_mul]
  congr 1
  exact Subtype.ext h

private theorem gen_mem_of_mul {x y z : modularFunctionFieldBar (N * q)} (hy : y ∈ R.R₁.integers)
    (hy0 : R.R₁.residue ⟨y, hy⟩ ≠ 0) (hz : z ∈ R.R₁.integers) (h : x * y = z) : x ∈ R.R₁.integers := by
  obtain ⟨b, hb⟩ := (R.R₁.isUnit_of_residue_ne_zero hy0).exists_right_inv
  have hb' : y * (b : modularFunctionFieldBar (N * q)) = 1 := by
    have := congrArg (fun w : R.R₁.integers => (w : modularFunctionFieldBar (N * q))) hb
    simpa using this
  have hx : x = z * (b : modularFunctionFieldBar (N * q)) := by
    rw [← h, mul_assoc, hb', mul_one]
  rw [hx]
  exact mul_mem hz b.2

include R in

private theorem gen_pack_res_ne_zero (x : CharPReduction.modularRing N A.toSubring)
    (hx : x ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)) :
    coeffMap (IsLocalRing.residue A)
      (packA_g A ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩) ≠ 0 := by
  intro h0
  apply CharPReduction.redRes_ne_zero_of_notMem hx
  rw [CharPReduction.redRes_apply, ← coeffMap_residue_packA_g]
  have hcomp : red = R.redBar.comp (IsLocalRing.residue A) := (RingHom.ext R.redBar_residue).symm
  rw [hcomp, ← coeffMap_coeffMap, h0, map_zero]

private theorem gen_alpha_pack (x : CharPReduction.modularRing N A.toSubring) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)
        ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        coeffMap (IsLocalRing.residue A)
          (packA_g A ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩) := by
  set xI : CharPReduction.integralCoeffs A.toSubring :=
    ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩ with hxI
  have hy : coeffMap A.subtype (packA_g A xI) ∈ modularFunctionFieldBar (N * q) := by
    rw [coeffMap_subtype_packA_g]
    have := (heckeAlphaBar (AlgebraicClosure ℚ) N q
      (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)).2
    rwa [coe_heckeAlphaBar] at this
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (packA_g A xI) hy
  have hel : (⟨coeffMap A.subtype (packA_g A xI), hy⟩ : modularFunctionFieldBar (N * q)) =
      heckeAlphaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N) := by
    apply Subtype.ext
    rw [coe_heckeAlphaBar]
    exact coeffMap_subtype_packA_g A xI
  have key : ∀ (e : modularFunctionFieldBar (N * q))
      (_ : e = (⟨coeffMap A.subtype (packA_g A xI), hy⟩ : modularFunctionFieldBar (N * q)))
      (h' : e ∈ R.R₁.integers),
      ((R.R₁.residue ⟨e, h'⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap (IsLocalRing.residue A) (packA_g A xI) := by
    rintro e rfl h'
    exact hres
  exact ⟨hel ▸ h, key _ hel.symm (hel ▸ h)⟩

private theorem gen_beta_pack (x : CharPReduction.modularRing N A.toSubring) :
    ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)
        ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        qExpand (IsLocalRing.ResidueField A) q (coeffMap (IsLocalRing.residue A)
          (packA_g A ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩)) := by
  set xI : CharPReduction.integralCoeffs A.toSubring :=
    ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩ with hxI
  set y : LaurentSeries A := qExpand A q (packA_g A xI) with hydef
  have hcoe : coeffMap A.subtype y = (heckeBetaBar (AlgebraicClosure ℚ) N q
      (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coe_heckeBetaBar, hydef, coeffMap_qExpand_g, coeffMap_subtype_packA_g]
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := by
    rw [hcoe]
    exact (heckeBetaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hy
  have hel : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) =
      heckeBetaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N) :=
    Subtype.ext hcoe
  have key : ∀ (e : modularFunctionFieldBar (N * q))
      (_ : e = (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q))) (h' : e ∈ R.R₁.integers),
      ((R.R₁.residue ⟨e, h'⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap (IsLocalRing.residue A) y := by
    rintro e rfl h'
    exact hres
  refine ⟨hel ▸ h, ?_⟩
  rw [key _ hel.symm (hel ▸ h), hydef, coeffMap_qExpand_g]

private theorem gen_beta_of_mem_localized (t : modularFunctionFieldBar N)
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) :
    ∃ hβ : heckeBetaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, hβ⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        qExpand (IsLocalRing.ResidueField A) q
          ((R.R₁.residue ⟨_, hα⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) := by
  obtain ⟨r, s, hs, hts⟩ := ht
  set rB : modularFunctionFieldBar N := ⟨r, modularRing_le_bar_g N A r.2⟩ with hrB
  set sB : modularFunctionFieldBar N := ⟨s, modularRing_le_bar_g N A s.2⟩ with hsB
  have htsB : t * sB = rB := Subtype.ext hts
  obtain ⟨hr₁, hrres⟩ := gen_alpha_pack (red := red) R r
  obtain ⟨hs₁, hsres⟩ := gen_alpha_pack (red := red) R s
  obtain ⟨hr₂, hrres'⟩ := gen_beta_pack (red := red) R r
  obtain ⟨hs₂, hsres'⟩ := gen_beta_pack (red := red) R s
  have hPs : coeffMap (IsLocalRing.residue A)
      (packA_g A ⟨s, CharPReduction.modularRing_le_integralCoeffs N A.toSubring s.2⟩) ≠ 0 :=
    gen_pack_res_ne_zero R s hs
  have hqPs : qExpand (IsLocalRing.ResidueField A) q (coeffMap (IsLocalRing.residue A)
      (packA_g A ⟨s, CharPReduction.modularRing_le_integralCoeffs N A.toSubring s.2⟩)) ≠ 0 := by
    intro h0
    apply hPs
    exact (qExpand_injective q) (by rw [h0, map_zero])
  have hsres₂ : R.R₁.residue ⟨_, hs₂⟩ ≠ 0 := by
    intro h0
    apply hqPs
    rw [← hsres', h0]
    rfl
  have hmulβ : heckeBetaBar (AlgebraicClosure ℚ) N q t * heckeBetaBar (AlgebraicClosure ℚ) N q sB =
      heckeBetaBar (AlgebraicClosure ℚ) N q rB := by rw [← map_mul, htsB]
  have hmulα : heckeAlphaBar (AlgebraicClosure ℚ) N q t * heckeAlphaBar (AlgebraicClosure ℚ) N q sB =
      heckeAlphaBar (AlgebraicClosure ℚ) N q rB := by rw [← map_mul, htsB]
  refine ⟨gen_mem_of_mul R hs₂ hsres₂ hr₂ hmulβ, ?_⟩

  have hα' := congrArg (fun w : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N =>
    (w : LaurentSeries (IsLocalRing.ResidueField A))) (gen_residue_mul R hα hs₁ hr₁ hmulα)
  have hβ' := congrArg (fun w : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N =>
    (w : LaurentSeries (IsLocalRing.ResidueField A))) (gen_residue_mul R (gen_mem_of_mul R hs₂ hsres₂ hr₂ hmulβ)
      hs₂ hr₂ hmulβ)
  beta_reduce at hα' hβ'
  push_cast at hα' hβ'
  rw [hsres, hrres] at hα'
  rw [hsres', hrres', ← hα', map_mul] at hβ'
  exact mul_right_cancel₀ hqPs hβ'

private theorem gen_inv_mem_localized (t : modularFunctionFieldBar N)
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) (hres : R.R₁.residue ⟨_, hα⟩ ≠ 0) :
    ((t⁻¹ : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized N A.toSubring red := by
  obtain ⟨r, s, hs, hts⟩ := ht
  have hres₁ : R.residue₁ ⟨_, hα⟩ ≠ 0 := by
    show R.ι (R.R₁.residue ⟨_, hα⟩) ≠ 0
    exact (map_ne_zero R.ι).mpr hres
  rw [localized_res_g R t r s hs hts hα] at hres₁
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing N A.toSubring) (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
    ⟨_, ⟨r, s, hs, hts⟩⟩ hts
  have hloc : CharPReduction.redLoc (A := A.toSubring) (red := red) (R := CharPReduction.modularRing N A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨_, ⟨r, s, hs, hts⟩⟩ ≠ 0 :=
    fun h0 => hres₁ (Subtype.ext h0)
  have hr : r ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) := by
    rw [CharPReduction.notMem_redKer_iff, ← hspec]
    exact mul_ne_zero hloc (CharPReduction.redRes_ne_zero_of_notMem hs)
  have ht0 : (t : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    apply hloc
    have hr0 : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) r = 0 := by
      have : (r : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [← hts, h0, zero_mul]
      have hr' : r = 0 := Subtype.ext this
      rw [hr', map_zero]
    exact absurd hr0 (CharPReduction.redRes_ne_zero_of_notMem hr)
  refine ⟨s, r, hr, ?_⟩
  rw [IntermediateField.coe_inv, inv_mul_eq_iff_eq_mul₀ ht0]
  exact hts.symm

private theorem gen_coe_mem_adjoin (t : modularFunctionFieldBar N) :
    (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N} := by
  have htop := adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N
  have ht : t ∈ (⊤ : IntermediateField (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := trivial
  rw [← htop] at ht
  have hmap : (modularFunctionFieldBar N).val t ∈
      (IntermediateField.adjoin (AlgebraicClosure ℚ) _).map (modularFunctionFieldBar N).val := ⟨t, ht, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_insert_eq, Set.image_singleton] at hmap
  have h1 : (modularFunctionFieldBar N).val ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = jqModC (AlgebraicClosure ℚ) :=
    coeffEmb_jq_eq_jqModC_g
  have h2 : (modularFunctionFieldBar N).val ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ =
        jqNModC (AlgebraicClosure ℚ) N := by
    show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N
    rw [jqNModC, ← coeffEmb_jq_eq_jqModC_g, coeffEmb, coeffMap_qExpand_g]
  rw [h1, h2] at hmap
  exact hmap

private theorem gen_mem_localized_of_alpha_mem (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) :
    (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red := by
  by_cases ht0 : t = 0
  · rw [ht0]
    exact zero_mem _
  obtain ⟨dataN⟩ := nonempty_modularPolynomialData N
  have hdeg := relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N q hqN
  rcases CharPReduction.mem_or_inv_mem_modularLocalized A red N dataN hdeg (gen_coe_mem_adjoin t) with h | h
  · exact h

  have hinv : ((t⁻¹ : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized N A.toSubring red := by
    rw [IntermediateField.coe_inv]
    exact h
  obtain ⟨hα', -⟩ := localized_glue_g R t⁻¹ hinv
  have hmul : heckeAlphaBar (AlgebraicClosure ℚ) N q t⁻¹ * heckeAlphaBar (AlgebraicClosure ℚ) N q t = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ht0, map_one]
  have hres : R.R₁.residue ⟨_, hα'⟩ ≠ 0 := by
    intro h0
    have h1 := gen_residue_mul R hα' hα (one_mem _) hmul
    rw [h0, zero_mul] at h1
    have h2 : R.R₁.residue ⟨(1 : modularFunctionFieldBar (N * q)), one_mem _⟩ = 1 := by
      rw [show (⟨(1 : modularFunctionFieldBar (N * q)), one_mem _⟩ : R.R₁.integers) = 1 from rfl, map_one]
    rw [h2] at h1
    exact zero_ne_one h1
  have := gen_inv_mem_localized R t⁻¹ hinv hα' hres
  rwa [inv_inv] at this

private theorem gen_alpha_mem_snd (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₂.integers := by
  obtain ⟨hβ, -⟩ := gen_beta_of_mem_localized R t (gen_mem_localized_of_alpha_mem R hqN t hα) hα
  rw [R.mem_integersSnd_iff, gen_atkinLehnerBar_heckeAlphaBar hqN]
  exact (R.mem_integersFst_iff _).mp hβ

private theorem gen_coe_residue_snd (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers)
    (h₂ : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₂.integers) :
    ((R.R₂.residue ⟨_, h₂⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) =
      qExpand (IsLocalRing.ResidueField A) q
        ((R.R₁.residue ⟨_, hα⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) := by
  obtain ⟨hβ, hβres⟩ := gen_beta_of_mem_localized R t (gen_mem_localized_of_alpha_mem R hqN t hα) hα
  have hw : ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q t) ∈ R.R₁.integers := by
    rw [gen_atkinLehnerBar_heckeAlphaBar hqN]
    exact hβ
  have hel : (⟨_, hw⟩ : R.R₁.integers) = ⟨heckeBetaBar (AlgebraicClosure ℚ) N q t, hβ⟩ :=
    Subtype.ext (gen_atkinLehnerBar_heckeAlphaBar hqN t)
  rw [R.residue₂_eq, hel]
  exact hβres

section ChartGenDivision

attribute [local instance] ChartGen.alongAlgebra ChartGen.alongTower

variable {v : Place k (modularFunctionFieldC k N)} {S : Set (modularFunctionFieldBar (N * q))}

include R in

private theorem gen_charP_residueField : CharP (IsLocalRing.ResidueField A) q :=
  RingHom.charP R.redBar R.redBar.injective q

include R in
private theorem gen_charP_fullC : CharP (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) q := by
  haveI := gen_charP_residueField R
  exact charP_of_injective_ringHom
    (algebraMap (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)).injective q

private theorem gen_hE₂ (hqN : ¬ q ∣ N) :
    ∀ e ∈ (heckeAlphaBar (AlgebraicClosure ℚ) N q).fieldRange, e ∈ R.R₁.integers → e ∈ R.R₂.integers := by
  intro e he h₁
  obtain ⟨t, rfl⟩ := AlgHom.mem_fieldRange.mp he
  exact gen_alpha_mem_snd R hqN t h₁

private theorem gen_exists_gauss_data (hqN : ¬ q ∣ N) {z : modularFunctionFieldBar (N * q)} (hz₂ : z ∈ R.R₂.integers)
    {n : ℤ} (hn : ¬ (q : ℤ) ∣ n)
    (hc : ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) :
    ∃ σ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N →+*
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N,
      (∀ e (he : e ∈ (heckeAlphaBar (AlgebraicClosure ℚ) N q).fieldRange) (h₁ : e ∈ R.R₁.integers),
        R.R₂.residue ⟨e, gen_hE₂ R hqN e he h₁⟩ = σ (R.R₁.residue ⟨e, h₁⟩)) ∧
      (∀ y, y ^ q ∈ σ.range) ∧
      (R.R₂.residue ⟨z, hz₂⟩ ∉ σ.range) ∧
      ∀ y, ((σ y : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        qExpand (IsLocalRing.ResidueField A) q (y : LaurentSeries (IsLocalRing.ResidueField A)) := by
  haveI := gen_charP_residueField R
  refine ⟨ChartGen.twist (IsLocalRing.ResidueField A) N q, ?_, ChartGen.pow_mem_range_twist _ N q, ?_,
    ChartGen.coe_twist _ N q⟩
  · intro e he h₁
    obtain ⟨t, rfl⟩ := AlgHom.mem_fieldRange.mp he
    apply Subtype.ext
    rw [ChartGen.coe_twist]
    exact gen_coe_residue_snd R hqN t h₁ _
  · refine ChartGen.notMem_range_twist_of_coeff_ne_zero _ N q hn ?_
    intro h0
    apply hc
    rw [R.residue₂_apply, R.ι_coe, coeffMap_coeff, h0, map_zero]

private theorem gen_powers_linearIndependent (hqN : ¬ q ∣ N)
    (z : modularFunctionFieldBar (N * q)) (hz₁ : z ∈ R.R₁.integers) (hz₂ : z ∈ R.R₂.integers)
    (hz : ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) :
    LinearIndependent (modularFunctionFieldBar N) fun i : Fin (q + 1) => z ^ (i : ℕ) := by
  haveI := gen_charP_fullC R
  obtain ⟨n, hn, hc⟩ := hz
  obtain ⟨σ, hσ, hpi, hzr, -⟩ := gen_exists_gauss_data R hqN hz₂ hn hc
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  simp only [Algebra.smul_def, ChartGen.algebraMap_along_apply] at hg
  have h0 := ChartGen.eq_zero_of_sum_mul_pow_eq_zero R.R₁ R.R₂ (gen_hE₂ R hqN) σ hσ Fact.out hpi hz₁ hz₂ hzr
    (fun i => heckeAlphaBar (AlgebraicClosure ℚ) N q (g i)) (fun i => AlgHom.mem_fieldRange.mpr ⟨g i, rfl⟩) hg i
  exact ChartGen.alpha_injective (h0.trans (map_zero (heckeAlphaBar (AlgebraicClosure ℚ) N q)).symm)

private theorem gen_generator_data (hqN : ¬ q ∣ N)
    (z : modularFunctionFieldBar (N * q)) (hz₁ : z ∈ R.R₁.integers) (hz₂ : z ∈ R.R₂.integers)
    (hz : ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) :
    IntermediateField.adjoin (AlgebraicClosure ℚ)
        (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤ ∧
      ∃ m : Polynomial (modularFunctionFieldBar N), m.Monic ∧ m.natDegree = q + 1 ∧
        (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0 ∧
        ∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ R.R₁.integers := by
  haveI := gen_charP_fullC R
  have hli := gen_powers_linearIndependent R hqN z hz₁ hz₂ hz
  obtain ⟨n, hn, hc⟩ := hz
  obtain ⟨σ, hσ, hpi, hzr, -⟩ := gen_exists_gauss_data R hqN hz₂ hn hc
  obtain ⟨hgen, m, hm, hdegm, hroot, hsum⟩ :=
    ChartGen.exists_monic_data_of_linearIndependent (ChartGen.finrankAlong_heckeAlphaBar_of_not_dvd N q hqN) z hli
  refine ⟨hgen, m, hm, hdegm, hroot, ?_⟩

  have hcoef := ChartGen.coeff_mem_integers_of_mem_integers R.R₁ R.R₂ (gen_hE₂ R hqN) σ hσ Fact.out hpi hz₁ hz₂ hzr
    (fun i => -(heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i)))
    (fun i => neg_mem (AlgHom.mem_fieldRange.mpr ⟨m.coeff i, rfl⟩)) hsum (pow_mem hz₁ _) (pow_mem hz₂ _)
  intro i
  rcases lt_trichotomy i (q + 1) with hi | rfl | hi
  · exact neg_mem_iff.mp (hcoef ⟨i, hi⟩)
  · rw [← hdegm, hm.coeff_natDegree, map_one]
    exact one_mem _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegm]; exact hi), map_zero]
    exact zero_mem _

private theorem gen_exists_residue_derivative_eq (hqN : ¬ q ∣ N)
    (z : modularFunctionFieldBar (N * q)) (hz₁ : z ∈ R.R₁.integers) (hz₂ : z ∈ R.R₂.integers)
    (hz : ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0)
    (m : Polynomial (modularFunctionFieldBar N)) (hm : m.Monic) (hdeg : m.natDegree = q + 1)
    (hroot : (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0)
    (hcoef : ∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ R.R₁.integers) :
    ∃ η : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N,
      qExpand (IsLocalRing.ResidueField A) q (η : LaurentSeries (IsLocalRing.ResidueField A)) =
          ((R.R₂.residue ⟨z, hz₂⟩ ^ q : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) ∧
        ∀ hD : (Polynomial.derivative (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom)).eval z
            ∈ R.R₁.integers,
          R.R₁.residue ⟨_, hD⟩ = R.R₁.residue ⟨z, hz₁⟩ ^ q - η := by
  haveI := gen_charP_fullC R
  obtain ⟨n, hn, hc⟩ := hz
  obtain ⟨σ, hσ, hpi, hzr, hcoe⟩ := gen_exists_gauss_data R hqN hz₂ hn hc
  obtain ⟨η, hη, hres⟩ := ChartGen.exists_residue_derivative_eval_eq_pow_sub R.R₁ R.R₂ (gen_hE₂ R hqN) σ hσ Fact.out hpi
    hz₂ hzr hz₁ (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom)
    (fun i => by rw [Polynomial.coeff_map]; exact AlgHom.mem_fieldRange.mpr ⟨m.coeff i, rfl⟩)
    (fun i => by rw [Polynomial.coeff_map]; exact hcoef i) (hm.map _) (by rw [hm.natDegree_map, hdeg]) hroot
  refine ⟨η, ?_, hres⟩
  rw [← hcoe, hη]

end ChartGenDivision
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"

private theorem aff_killer_of_value [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hu₀v : P.sp u₀ ≠ v) (a₀ : A)
    (ha₀ : 0 < u₀.ord (CharPModel.jBar N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ))) :
    ∃ b : fm.BFin, 0 < u₀.ord (b : modularFunctionFieldBar N) ∧ ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin b) t := by
  have hsp1 : jGeomGen k N ∈ (P.sp u₀).toValuationSubring :=
    ((P.sp u₀).hasValue_of_ord_sub_pos_pn (P.d0_j u₀ a₀ ha₀)).mem
  obtain ⟨b, hbsp, hbv⟩ := aff_exists_separator fm hqN v (P.sp u₀) hv1 hsp1 hu₀v
  obtain ⟨c, hu₀c, hspc⟩ := aff_bfin_values fm hred dataAll hsep hP hqN (P.sp u₀) hsp1 b u₀ rfl
  have hc0 : red c = 0 := hspc.unique hbsp
  set b' : fm.BFin := b - ⟨CharPModel.constantsHom N A c, fm.constFin_mem c⟩ with hb'
  have hb'coe : (b' : modularFunctionFieldBar N)
      = (b : modularFunctionFieldBar N) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c : AlgebraicClosure ℚ) := by
    rw [hb']
    push_cast
    rfl
  have hpi : fm.piFin b' = fm.piFin b := by
    rw [hb', map_sub, fm.piFin_const, hc0, map_zero, sub_zero]
  refine ⟨b', ?_, ?_⟩
  · have hne0 : (b' : modularFunctionFieldBar N) ≠ 0 := by
      intro h0
      have hb'0 : b' = 0 := Subtype.ext h0
      have hpi0 : fm.piFin b = 0 := by
        rw [← hpi, hb'0, map_zero]
      apply hbv
      rw [hpi0]
      have h1 := v.hasValue_algebraMap (0 : k)
      rwa [map_zero] at h1
    have h2 := aff_sub_mem_nonunits_of_hasValue u₀ hu₀c
    rw [← hb'coe] at h2
    have hmem : (b' : modularFunctionFieldBar N) ∈ u₀.toValuationSubring := by
      rw [hb'coe]
      exact sub_mem hu₀c.mem (u₀.algebraMap_mem' _)
    have hmax : (⟨_, hmem⟩ : u₀.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      ValuationSubring.coe_mem_nonunits_iff.mp h2
    exact (u₀.mem_maximalIdeal_iff_ord_pos hne0 hmem).mp hmax
  · rw [hpi]
    obtain ⟨t, ht, -⟩ := v.exists_hasValue_of_surjective (aff_residue_surjective v)
      ((aff_FIN N A q hqN k red fm v hv1).1 b)
    exact ⟨t, fun ht0 => hbv (ht0 ▸ ht), ht⟩

private theorem aff_killer_of_no_value [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hu₀j : CharPModel.jBar N ∈ u₀.toValuationSubring)
    (hA : ¬ ∃ a₀ : A, 0 < u₀.ord (CharPModel.jBar N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ))) :
    ∃ b : fm.BFin, 0 < u₀.ord (b : modularFunctionFieldBar N) ∧ ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin b) t := by
  obtain ⟨t₀, ht₀, -⟩ := u₀.exists_hasValue_of_surjective (aff_bar_residue_surjective u₀) hu₀j

  have ht₀A : ∀ a : A, (a : AlgebraicClosure ℚ) ≠ t₀ := by
    intro a ha
    apply hA
    refine ⟨a, ?_⟩
    rw [ha]
    have hne := sub_ne_zero.mpr (aff_jBar_ne_algebraMap (N := N) t₀)
    have hmem : CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) t₀ ∈ u₀.toValuationSubring :=
      sub_mem ht₀.mem (u₀.algebraMap_mem' _)
    have hmax : (⟨_, hmem⟩ : u₀.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      ValuationSubring.coe_mem_nonunits_iff.mp (aff_sub_mem_nonunits_of_hasValue u₀ ht₀)
    exact (u₀.mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax
  have ht₀0 : t₀ ≠ 0 := fun h => ht₀A 0 (by simp [h])
  have hinvA : t₀⁻¹ ∈ A := (A.mem_or_inv_mem t₀).resolve_left fun hmem => ht₀A ⟨t₀, hmem⟩ rfl

  have ha₁m : (⟨t₀⁻¹, hinvA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨d, hd⟩ := hunit.exists_right_inv
    have h3 : t₀⁻¹ * (d : AlgebraicClosure ℚ) = 1 := congrArg Subtype.val hd
    exact ht₀A d ((inv_mul_eq_one₀ ht₀0).mp h3).symm
  have hred0 : red ⟨t₀⁻¹, hinvA⟩ = 0 := aff_red_eq_zero_of_mem_maximalIdeal hred ha₁m
  set b : fm.BFin := 1 - ⟨CharPModel.constantsHom N A ⟨t₀⁻¹, hinvA⟩, fm.constFin_mem _⟩ * ⟨CharPModel.jBar N, fm.jBar_mem⟩
    with hb
  have hbcoe : (b : modularFunctionFieldBar N)
      = 1 - CharPModel.constantsHom N A ⟨t₀⁻¹, hinvA⟩ * CharPModel.jBar N := by
    rw [hb]
    first
      | (push_cast; done)
      | (push_cast; rfl)
      | rfl
  have hc : u₀.HasValue (CharPModel.constantsHom N A ⟨t₀⁻¹, hinvA⟩) t₀⁻¹ := u₀.hasValue_algebraMap t₀⁻¹
  refine ⟨b, ?_, 1, one_ne_zero, ?_⟩
  ·
    have hval : u₀.HasValue (b : modularFunctionFieldBar N) (1 - t₀⁻¹ * t₀) := by
      rw [hbcoe, sub_eq_add_neg, sub_eq_add_neg]
      exact plv_hasValue_add u₀ u₀.hasValue_one (plv_hasValue_neg u₀ (hc.mul ht₀))
    rw [inv_mul_cancel₀ ht₀0, sub_self] at hval
    have hne0 : (b : modularFunctionFieldBar N) ≠ 0 := by
      intro h0
      rw [hbcoe] at h0
      have h0' : (1 : modularFunctionFieldBar N)
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) t₀⁻¹ * CharPModel.jBar N := sub_eq_zero.mp h0
      have h4 : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) t₀⁻¹)⁻¹ = CharPModel.jBar N :=
        inv_eq_of_mul_eq_one_right h0'.symm
      rw [map_inv₀, inv_inv] at h4
      exact aff_jBar_ne_algebraMap (N := N) t₀ h4.symm
    have hmax : (⟨_, hval.mem⟩ : u₀.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
      have h5 := aff_sub_mem_nonunits_of_hasValue u₀ hval
      rw [map_zero, sub_zero] at h5
      exact ValuationSubring.coe_mem_nonunits_iff.mp h5
    exact (u₀.mem_maximalIdeal_iff_ord_pos hne0 hval.mem).mp hmax
  ·
    have hpi : fm.piFin b = 1 := by
      rw [hb, fm.piFin.map_sub, fm.piFin.map_one, fm.piFin.map_mul, fm.piFin_const, hred0,
        (algebraMap k (modularFunctionFieldC k N)).map_zero, zero_mul, sub_zero]
    rw [hpi]
    exact v.hasValue_one

private theorem aff_exists_killer [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hu₀j : CharPModel.jBar N ∈ u₀.toValuationSubring)
    (hu₀v : P.sp u₀ ≠ v) :
    ∃ b : fm.BFin, 0 < u₀.ord (b : modularFunctionFieldBar N) ∧ ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin b) t := by
  by_cases hA : ∃ a₀ : A, 0 < u₀.ord (CharPModel.jBar N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ))
  · obtain ⟨a₀, ha₀⟩ := hA
    exact aff_killer_of_value fm hred dataAll hsep hP hqN v hv1 u₀ hu₀v a₀ ha₀
  · exact aff_killer_of_no_value fm hred dataAll hsep hP hqN v hv1 u₀ hu₀j hA

private theorem aff_ne_zero_of_value (fm : FibreModel N A q k red) (v : Place k (modularFunctionFieldC k N))
    {e : fm.BFin} {t : k} (ht0 : t ≠ 0) (ht : v.HasValue (fm.piFin e) t) : (e : modularFunctionFieldBar N) ≠ 0 := by
  intro h0
  have he : e = 0 := Subtype.ext h0
  rw [he, map_zero] at ht
  have h1 := v.hasValue_algebraMap (0 : k)
  rw [map_zero] at h1
  exact ht0 (ht.unique h1)

private theorem aff_value_mul (fm : FibreModel N A q k red) (v : Place k (modularFunctionFieldC k N)) {e e' : fm.BFin}
    (h : ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin e) t) (h' : ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin e') t) :
    ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin (e * e')) t := by
  obtain ⟨t, ht0, ht⟩ := h
  obtain ⟨t', ht0', ht'⟩ := h'
  refine ⟨t * t', mul_ne_zero ht0 ht0', ?_⟩
  rw [map_mul]
  exact ht.mul ht'

private theorem aff_value_pow (fm : FibreModel N A q k red) (v : Place k (modularFunctionFieldC k N)) {e : fm.BFin}
    (h : ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin e) t) (n : ℕ) :
    ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin (e ^ n)) t := by
  obtain ⟨t, ht0, ht⟩ := h
  refine ⟨t ^ n, pow_ne_zero n ht0, ?_⟩
  rw [map_pow]
  exact aff_hasValue_pow v ht n

private theorem aff_ord_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F) (f : F) (n : ℕ) :
    u.ord (f ^ n) = n * u.ord f := by
  rw [← zpow_natCast, u.ord_zpow]

private theorem aff_exists_clearing_aux [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (n : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℕ)
    (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (hT : ∀ u ∈ T, CharPModel.jBar N ∈ u.toValuationSubring ∧ P.sp u ≠ v) :
    ∃ e : fm.BFin, (∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin e) t) ∧
      ∀ u ∈ T, (n u : ℤ) ≤ u.ord (e : modularFunctionFieldBar N) := by
  classical
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    refine ⟨1, ⟨1, one_ne_zero, ?_⟩, fun u hu => absurd hu (by simp)⟩
    rw [map_one]
    exact v.hasValue_one
  · intro u T huT ih hT
    obtain ⟨e₁, he₁, hbound⟩ := ih fun w hw => hT w (Finset.mem_insert_of_mem hw)
    obtain ⟨huj, huv⟩ := hT u (Finset.mem_insert_self u T)
    obtain ⟨b, hbu, hbval⟩ := aff_exists_killer fm hred dataAll hsep hP hqN v hv1 u huj huv
    refine ⟨b ^ n u * e₁, aff_value_mul fm v (aff_value_pow fm v hbval _) he₁, ?_⟩
    have hcoe : ((b ^ n u * e₁ : fm.BFin) : modularFunctionFieldBar N)
        = (b : modularFunctionFieldBar N) ^ n u * (e₁ : modularFunctionFieldBar N) := by
      simp
    have hb0 : (b : modularFunctionFieldBar N) ≠ 0 := u.ne_zero_of_ord_pos_pn hbu
    obtain ⟨t₁, ht₁0, ht₁⟩ := he₁
    have he₁0 : (e₁ : modularFunctionFieldBar N) ≠ 0 := aff_ne_zero_of_value fm v ht₁0 ht₁
    intro w hw
    rw [hcoe, w.ord_mul (pow_ne_zero _ hb0) he₁0, aff_ord_pow]
    rcases Finset.mem_insert.mp hw with hwu | hwT
    ·
      rw [hwu]
      have h1 : (0 : ℤ) ≤ u.ord (e₁ : modularFunctionFieldBar N) :=
        u.ord_nonneg_of_mem_pn (aff_bfin_mem_of_jBar_mem fm e₁ u huj)
      have h2 : (n u : ℤ) * 1 ≤ (n u : ℤ) * u.ord (b : modularFunctionFieldBar N) :=
        mul_le_mul_of_nonneg_left hbu (Int.natCast_nonneg _)
      linarith
    ·
      have h1 : (0 : ℤ) ≤ w.ord (b : modularFunctionFieldBar N) :=
        w.ord_nonneg_of_mem_pn (aff_bfin_mem_of_jBar_mem fm b w (hT w (Finset.mem_insert_of_mem hwT)).1)
      have h2 : (0 : ℤ) ≤ (n u : ℤ) * w.ord (b : modularFunctionFieldBar N) :=
        mul_nonneg (Int.natCast_nonneg _) h1
      have h3 := hbound w hwT
      linarith

private theorem aff_exists_clearing [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (φ : modularFunctionFieldBar N)
    (hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u₀ = v → φ ∈ u₀.toValuationSubring) :
    ∃ e : fm.BFin, (∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piFin e) t) ∧
      ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        CharPModel.jBar N ∈ u₀.toValuationSubring → φ * (e : modularFunctionFieldBar N) ∈ u₀.toValuationSubring := by
  classical
  by_cases hφ0 : φ = 0
  · refine ⟨1, ⟨1, one_ne_zero, ?_⟩, fun u₀ _ => ?_⟩
    · rw [map_one]
      exact v.hasValue_one
    · rw [hφ0, zero_mul]
      exact zero_mem _
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) φ hφ0
  set T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    D.support.filter (fun u => CharPModel.jBar N ∈ u.toValuationSubring ∧ u.ord φ < 0) with hT
  have hTprop : ∀ u ∈ T, CharPModel.jBar N ∈ u.toValuationSubring ∧ P.sp u ≠ v := by
    intro u hu
    obtain ⟨-, huj, huord⟩ := Finset.mem_filter.mp hu
    refine ⟨huj, fun huv => ?_⟩
    have := u.ord_nonneg_of_mem_pn (hreg u huv)
    omega
  obtain ⟨e, he, hbound⟩ := aff_exists_clearing_aux fm hred dataAll hsep hP hqN v hv1 (fun u => (-u.ord φ).toNat) T hTprop
  refine ⟨e, he, fun u₀ hu₀ => ?_⟩
  have he_mem : (e : modularFunctionFieldBar N) ∈ u₀.toValuationSubring := aff_bfin_mem_of_jBar_mem fm e u₀ hu₀
  by_cases hpole : u₀.ord φ < 0
  · have hu₀T : u₀ ∈ T := by
      rw [hT, Finset.mem_filter, Finsupp.mem_support_iff, hD u₀]
      exact ⟨by omega, hu₀, hpole⟩
    have h1 : (((-u₀.ord φ).toNat : ℕ) : ℤ) ≤ u₀.ord (e : modularFunctionFieldBar N) := hbound u₀ hu₀T
    rw [Int.toNat_of_nonneg (by omega)] at h1
    obtain ⟨t, ht0, ht⟩ := he
    have he0 : (e : modularFunctionFieldBar N) ≠ 0 := aff_ne_zero_of_value fm v ht0 ht
    refine u₀.mem_of_ord_nonneg_pn (mul_ne_zero hφ0 he0) ?_
    rw [u₀.ord_mul hφ0 he0]
    omega
  · exact mul_mem (u₀.mem_of_ord_nonneg_pn hφ0 (not_lt.mp hpole)) he_mem

private theorem aff_nIncl [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (hBFC : ∀ s : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N),
      (∃ p : Polynomial (CharPModel.affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (CharPModel.affineBaseFin N A).subtype s p = 0) → s ∈ fm.BFin)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (hint : ∀ s ∈ aff_S fm, s ∈ R.R₁.integers)
    (φ : modularFunctionFieldBar N) (hφ : heckeAlphaBar (AlgebraicClosure ℚ) N q φ ∈ R.R₁.integers)
    (hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u₀ = v → φ ∈ u₀.toValuationSubring) :
    ∃ (s : modularFunctionFieldBar (N * q)) (_ : s ∈ aff_S fm) (e : modularFunctionFieldBar (N * q)) (he : e ∈ aff_S fm),
      ¬ v.HasValue (R.residue₁ ⟨e, hint e he⟩) (0 : k) ∧ heckeAlphaBar (AlgebraicClosure ℚ) N q φ * e = s := by
  obtain ⟨e₀, ⟨t, ht0, ht⟩, hclear⟩ := aff_exists_clearing fm hred dataAll hsep hP hqN v hv1 φ hreg

  obtain ⟨he₀I, he₀res⟩ := aff_residue_alpha R fm e₀
  have hψint : heckeAlphaBar (AlgebraicClosure ℚ) N q (φ * (e₀ : modularFunctionFieldBar N)) ∈ R.R₁.integers := by
    rw [map_mul]
    exact mul_mem hφ he₀I
  have hψloc : ((φ * (e₀ : modularFunctionFieldBar N) : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    have h := (R.mem_integersFst_iff _).mp hψint
    rwa [coe_heckeAlphaBar] at h
  have hψB : φ * (e₀ : modularFunctionFieldBar N) ∈ fm.BFin :=
    hBFC _ (aff_GLN red hqN _ hψloc hclear)
  refine ⟨_, aff_alpha_mem fm ⟨_, hψB⟩, _, aff_alpha_mem fm e₀, ?_, ?_⟩
  · have hres : R.residue₁ ⟨_, hint _ (aff_alpha_mem fm e₀)⟩ = fm.piFin e₀ := he₀res
    rw [hres]
    exact aff_not_hasValue_zero_of_ne v ht ht0
  · exact (map_mul (heckeAlphaBar (AlgebraicClosure ℚ) N q) φ (e₀ : modularFunctionFieldBar N)).symm

private theorem finrankAlong_algEquiv_toAlgHom {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃ₐ[K] F') : finrankAlong K e.toAlgHom = 1 := by
  have h := finrankAlong_comp e.toAlgHom e.symm.toAlgHom
  have hid : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K F := by
    ext x
    simp
  rw [hid, finrankAlong_id] at h
  first
    | exact Nat.eq_one_of_mul_eq_one_right h.symm
    | exact (Nat.mul_eq_one.mp h.symm).1
    | exact (mul_eq_one.mp h.symm).1

private theorem _root_.ModularCurve.PlaceSpecialization.finrankAlong_heckeAlphaBar_of_not_dvd (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1 := by
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q σ hσ).1
  have hβ := finrankAlong_heckeBetaBar (AlgebraicClosure ℚ) N q
  rw [if_neg hqN, ← hlegs, finrankAlong_comp, finrankAlong_algEquiv_toAlgHom, mul_one] at hβ
  exact hβ

p2m_export "ModularCurve.PlaceSpecialization" "finrankAlong_heckeAlphaBar_of_not_dvd"

private theorem atkinLehnerBar_heckeBetaBar_g (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q t) =
      heckeAlphaBar (AlgebraicClosure ℚ) N q t := by
  have hex := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ).2
  exact AlgHom.congr_fun hlegs t

private theorem aff_beta_mem_snd (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin) :
    heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ R.R₂.integers := by
  obtain ⟨hαI, -⟩ := aff_residue_alpha R fm b
  rw [R.mem_integersSnd_iff, atkinLehnerBar_heckeBetaBar_g hqN]
  exact (R.mem_integersFst_iff _).mp hαI

private theorem aff_residue₂_beta (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin)
    (h : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ = fm.piFin b := by
  obtain ⟨hαI, hαres⟩ := aff_residue_alpha R fm b
  have hAL := atkinLehnerBar_heckeBetaBar_g hqN (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
  have h2 : R.residue₂ ⟨_, h⟩ = R.residue₁ ⟨_, hαI⟩ := by
    show R.ι (R.R₂.residue ⟨_, h⟩) = R.ι (R.R₁.residue ⟨_, hαI⟩)
    rw [R.residue₂_eq]
    exact congrArg R.ι (congrArg R.R₁.residue (Subtype.ext hAL))
  rw [h2, hαres]

private theorem aff_frob_ι_eq (z : modularFunctionFieldBar (N * q)) (hz₂ : z ∈ R.R₂.integers)
    (η : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
    (hη : qExpand (IsLocalRing.ResidueField A) q (η : LaurentSeries (IsLocalRing.ResidueField A)) =
      ((R.R₂.residue ⟨z, hz₂⟩ ^ q : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A))) :
    frobeniusGeomLevel k N data hKr (R.ι η) = R.residue₂ ⟨z, hz₂⟩ ^ q := by
  apply Subtype.ext
  rw [frobeniusGeomLevel_apply_coe, R.ι_coe, ← coeffMap_qExpand, hη]
  push_cast
  rw [map_pow, ← R.ι_coe]
  rfl

private theorem aff_etale_line [IsAlgClosed k] (w : Place k (modularFunctionFieldC k N)) (ybar ηbar : modularFunctionFieldC k N)
    (hη : frobeniusGeomLevel k N data hKr ηbar = ybar ^ q) {t₁ t₂ : k} (hne : t₁ ≠ t₂)
    (h₁ : w.HasValue ybar t₁)
    (h₂ : (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w)).HasValue ybar t₂) :
    ¬ (frobOnPlacesGeomLevel k N data hKr w).HasValue (frobeniusGeomLevel k N data hKr ybar ^ q - ηbar) (0 : k) := by
  intro h0
  haveI : CharP (modularFunctionFieldC k N) q := charP_modularFunctionFieldC k N
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero

  have h3 := aff_hasValue_frob_apply w h0
  rw [map_sub, map_pow, hη, ← sub_pow_char] at h3
  have h4 : frobeniusGeomLevel k N data hKr (frobeniusGeomLevel k N data hKr ybar) - ybar ∈ w.toValuationSubring.nonunits := by
    have h5 := aff_sub_mem_nonunits_of_hasValue w h3
    rw [map_zero, sub_zero] at h5
    exact aff_mem_nonunits_of_pow_mem w hq h5
  have h6 : w.HasValue (frobeniusGeomLevel k N data hKr (frobeniusGeomLevel k N data hKr ybar) - ybar) (0 : k) := by
    refine aff_hasValue_of_sub_mem_nonunits w ?_
    rwa [map_zero, sub_zero]

  have h7 : w.HasValue (frobeniusGeomLevel k N data hKr (frobeniusGeomLevel k N data hKr ybar) - ybar) (t₂ - t₁) := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact plv_hasValue_add w (aff_hasValue_frob_apply w (aff_hasValue_frob_apply _ h₂)) (plv_hasValue_neg w h₁)
  exact hne (sub_eq_zero.mp (h7.unique h6)).symm

private theorem aff_exists_candidate [IsAlgClosed k] (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    (w : Place k (modularFunctionFieldC k N)) (hwaff : IsAffineGeomPlace k N w)
    (hw2 : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w) :
    ∃ y : fm.BFin,
      (∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧ ((fm.piFin y : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) ∧
      ∃ t₁ t₂ : k, t₁ ≠ t₂ ∧ w.HasValue (fm.piFin y) t₁ ∧ (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w)).HasValue (fm.piFin y) t₂ := by
  classical
  have hw2aff : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w)) :=
    aff_isAffine_frob_of_isAffine _ (aff_isAffine_frob_of_isAffine w hwaff)
  obtain ⟨c, hc2, hcw⟩ := aff_exists_separator fm hqN w _ hwaff.1 hw2aff.1 hw2
  obtain ⟨t, ht, -⟩ := w.exists_hasValue_of_surjective (aff_residue_surjective w)
    ((aff_FIN N A q hqN k red fm w hwaff.1).1 c)
  have ht0 : t ≠ 0 := fun h => hcw (h ▸ ht)
  by_cases hcoeff : ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧ ((fm.piFin c : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0
  · exact ⟨c, hcoeff, t, 0, ht0, ht, hc2⟩

  have hc0 : ∀ n : ℤ, ¬ (q : ℤ) ∣ n → ((fm.piFin c : modularFunctionFieldC k N) : LaurentSeries k).coeff n = 0 :=
    fun n hn => by_contra fun h => hcoeff ⟨n, hn, h⟩
  have hN : ¬ (q : ℤ) ∣ -(N : ℤ) := by
    rw [dvd_neg]
    exact_mod_cast hqN

  set yN : fm.BFin := ⟨CharPModel.jNBar N, fm.jNBar_mem⟩
  have hpiN : fm.piFin yN = jNGeomGen k N := fm.piFin_jN
  have hcoeffN : ((jNGeomGen k N : modularFunctionFieldC k N) : LaurentSeries k).coeff (-(N : ℤ)) = 1 := by
    rw [coe_jNGeomGen, jqNModC, show (-(N : ℤ)) = (N : ℤ) * (-1) by ring, qExpand_coeff_mul, coeff_jqModC_neg_one]

  obtain ⟨d₁, hd₁, -⟩ := w.exists_hasValue_of_surjective (aff_residue_surjective w) hwaff.2
  obtain ⟨d₂, hd₂, -⟩ := (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w)).exists_hasValue_of_surjective (aff_residue_surjective _) hw2aff.2
  by_cases hd : d₁ = d₂
  ·
    refine ⟨yN + c, ⟨-(N : ℤ), hN, ?_⟩, d₁ + t, d₂ + 0, ?_, ?_, ?_⟩
    · rw [map_add, hpiN]
      rw [IntermediateField.coe_add, HahnSeries.coeff_add, hcoeffN, hc0 _ hN, add_zero]
      exact one_ne_zero
    · rw [hd]
      intro h
      exact ht0 (add_left_cancel h)
    · rw [map_add, hpiN]
      exact plv_hasValue_add w hd₁ ht
    · rw [map_add, hpiN]
      exact plv_hasValue_add _ hd₂ hc2
  ·
    refine ⟨yN, ⟨-(N : ℤ), hN, ?_⟩, d₁, d₂, hd, ?_, ?_⟩
    · rw [hpiN, hcoeffN]
      exact one_ne_zero
    · rw [hpiN]
      exact hd₁
    · rw [hpiN]
      exact hd₂

omit [Fact (Nat.Prime q)] [NeZero N] in

private theorem aff_mem_restrictAlong_iff (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (x : modularFunctionFieldBar N) :
    x ∈ (W.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ W.toValuationSubring := by
  by_cases hx : x = 0
  · subst hx
    rw [map_zero]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  have hφx : φ x ≠ 0 := (map_ne_zero φ).mpr hx
  have he : (0 : ℤ) < (Place.ramificationIndexAlong φ W : ℤ) := by
    exact_mod_cast aff_ramificationIndexAlong_pos' φ hφ W
  constructor
  · intro h
    refine W.mem_of_ord_nonneg_pn hφx ?_
    rw [W.ord_restrictAlong φ hφ x]
    exact mul_nonneg he.le ((W.restrictAlong φ hφ).ord_nonneg_of_mem_pn h)
  · intro h
    have h1 := W.ord_nonneg_of_mem_pn h
    rw [W.ord_restrictAlong φ hφ x] at h1
    refine (W.restrictAlong φ hφ).mem_of_ord_nonneg_pn hx ?_
    by_contra hneg
    have h2 := mul_neg_of_pos_of_neg he (not_le.mp hneg)
    linarith

private theorem aff_beta_jBar_isIntegral (dq : ModularPolynomialData q) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)} : Set (modularFunctionFieldBar (N * q))))
      (heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)) := by
  let ev : Polynomial ℤ →+* Algebra.adjoin (AlgebraicClosure ℚ) ({heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)} : Set (modularFunctionFieldBar (N * q))) :=
    (Polynomial.aeval (⟨heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N), Algebra.subset_adjoin (Set.mem_singleton _)⟩ :
      Algebra.adjoin (AlgebraicClosure ℚ) ({heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)} : Set (modularFunctionFieldBar (N * q))))).toRingHom
  refine ⟨dq.Φ.map ev, dq.monic.map ev, ?_⟩
  have key : (modularFunctionFieldBar (N * q)).val.toRingHom
      (Polynomial.eval₂ (algebraMap _ (modularFunctionFieldBar (N * q))) (heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)) (dq.Φ.map ev)) = 0 := by
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
    have hcomp : ((modularFunctionFieldBar (N * q)).val.toRingHom.comp (algebraMap _ (modularFunctionFieldBar (N * q)))).comp ev
        = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      show ((algebraMap _ (modularFunctionFieldBar (N * q)) (ev Polynomial.X) : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffEmb (AlgebraicClosure ℚ) (evalAtJ Polynomial.X)
      have hX : ev Polynomial.X = ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N), Algebra.subset_adjoin (Set.mem_singleton _)⟩ :=
        Polynomial.aeval_X _
      rw [evalAtJ_X, hX]
      show ((heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq
      exact coe_heckeAlphaBar ..
    rw [hcomp]
    have hβ : (modularFunctionFieldBar (N * q)).val.toRingHom (heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)) = coeffEmb (AlgebraicClosure ℚ) (jqN q) := by
      rw [jqN, coeffEmb_qExpand_aux]
      exact coe_heckeBetaBar ..
    rw [hβ, ← Polynomial.hom_eval₂, dq.eval_eq_zero, map_zero]
  exact Subtype.ext key

include hβ in

private theorem aff_beta_regular (dq : ModularPolynomialData q) (fm : FibreModel N A q k red) (y : fm.BFin)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hu₀ : CharPModel.jBar N ∈ u₀.toValuationSubring)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = u₀) :
    heckeBetaBar (AlgebraicClosure ℚ) N q (y : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ W.toValuationSubring := by
  have hαj : heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ W.toValuationSubring := by
    refine (aff_mem_restrictAlong_iff _ hα W _).mp ?_
    rw [hW]
    exact hu₀
  have hβj : heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ W.toValuationSubring :=
    W.mem_toValuationSubring_of_isIntegral_adjoin hαj (aff_beta_jBar_isIntegral dq)
  have hj' : CharPModel.jBar N ∈ (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).toValuationSubring :=
    (aff_mem_restrictAlong_iff _ hβ W _).mpr hβj
  exact (aff_mem_restrictAlong_iff _ hβ W _).mp (aff_bfin_mem_of_jBar_mem fm y _ hj')

private theorem aff_etale_coeffs (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    (hBFC : ∀ s : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N),
      (∃ p : Polynomial (CharPModel.affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (CharPModel.affineBaseFin N A).subtype s p = 0) → s ∈ fm.BFin)
    (m : Polynomial (modularFunctionFieldBar N))
    (hcoef : ∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ R.R₁.integers)
    (hcreg : ∀ (i : ℕ) (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      CharPModel.jBar N ∈ u₀.toValuationSubring → m.coeff i ∈ u₀.toValuationSubring) :
    ∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ Subring.closure (aff_S fm) := by
  intro i
  have hloc : ((m.coeff i : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    have h := (R.mem_integersFst_iff _).mp (hcoef i)
    rwa [coe_heckeAlphaBar] at h
  have hB : m.coeff i ∈ fm.BFin := hBFC _ (aff_GLN red hqN _ hloc (hcreg i))
  exact Subring.subset_closure (aff_alpha_mem fm ⟨_, hB⟩)

set_option maxHeartbeats 1600000 in

private theorem aff_etale [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (hBFC : ∀ s : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N),
      (∃ p : Polynomial (CharPModel.affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (CharPModel.affineBaseFin N A).subtype s p = 0) → s ∈ fm.BFin)
    (v : Place k (modularFunctionFieldC k N)) (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) (hvaff : IsAffineGeomPlace k N v) :
    ChartEtaleAt R v (aff_S fm) := by
  obtain ⟨w, hw⟩ := frobOnPlacesGeomLevel_surjective k N data hKr
    (fun c => IsAlgClosed.exists_pow_nat_eq c (Fact.out : q.Prime).pos) v
  have hw2 : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w := fun h => hv (by
    rw [← hw]
    exact congrArg (frobOnPlacesGeomLevel k N data hKr) h)
  have hwaff : IsAffineGeomPlace k N w := aff_isAffine_of_isAffine_frob w (by
    rw [hw]
    exact hvaff)
  obtain ⟨y, hycoeff, t₁, t₂, hne, h₁, h₂⟩ := aff_exists_candidate fm hqN w hwaff hw2
  obtain ⟨hz₁, hres₁⟩ := aff_residue_beta R fm y
  have hz₂ : heckeBetaBar (AlgebraicClosure ℚ) N q (y : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ R.R₂.integers := aff_beta_mem_snd R hqN fm y
  have hres₂ : R.residue₂ ⟨_, hz₂⟩ = fm.piFin y := aff_residue₂_beta R hqN fm y hz₂
  have hz : ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨_, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0 := by
    rw [hres₂]
    exact hycoeff
  obtain ⟨hgen, m, hm, hdegm, hroot, hcoef⟩ := gen_generator_data R hqN _ hz₁ hz₂ hz
  obtain ⟨η, hη, hD⟩ := gen_exists_residue_derivative_eq R hqN _ hz₁ hz₂ hz m hm hdegm hroot hcoef
  have hcreg := ChartGen.coeff_mem_of_forall_mem_affine hα (finrankAlong_heckeAlphaBar_of_not_dvd N q hqN) _ hgen
    m hm hdegm hroot (fun u₀ hu₀ W hW => aff_beta_regular (hβ := hβ) data fm y u₀ hu₀ W hW)
  refine ⟨_, m, aff_beta_mem fm y, ⟨hz₂, hz⟩, hgen, hm, hdegm, hroot, aff_etale_coeffs R fm hqN hBFC m hcoef hcreg, ?_⟩
  ·
    intro hder
    have hres₁' : R.ι (R.R₁.residue ⟨_, hz₁⟩) = frobeniusGeomLevel k N data hKr (fm.piFin y) := hres₁
    have hζ : R.residue₁ ⟨_, hder⟩ = frobeniusGeomLevel k N data hKr (fm.piFin y) ^ q - R.ι η := by
      show R.ι (R.R₁.residue ⟨_, hder⟩) = _
      rw [hD hder, map_sub, map_pow, hres₁']
    have hη' : frobeniusGeomLevel k N data hKr (R.ι η) = fm.piFin y ^ q :=
      (aff_frob_ι_eq R _ hz₂ η hη).trans (congrArg (fun t => t ^ q) hres₂)
    rw [hζ, ← hw]
    exact aff_etale_line w (fm.piFin y) (R.ι η) hη' hne h₁ h₂

private theorem exists_isChartAt_affine [IsAlgClosed k] (fm : FibreModel N A q k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (hBFC : ∀ s : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N),
      (∃ p : Polynomial (CharPModel.affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (CharPModel.affineBaseFin N A).subtype s p = 0) → s ∈ fm.BFin) :
    ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      IsAffineGeomPlace k N v →
      ∃ S : Set (modularFunctionFieldBar (N * q)), IsChartAt R v S := by
  intro v hv hvaff
  have hgood : ∀ s ∈ aff_S fm, aff_Good R v s := fun s hs =>
    aff_good_of_mem R fm hred dataAll hsep hP hqN v hvaff hs
  have hint : ∀ s ∈ aff_S fm, s ∈ R.R₁.integers := fun s hs => (hgood s hs).choose
  exact ⟨aff_S fm,
    { integral := hint
      regular := fun s hs => (hgood s hs).choose_spec.1
      gens_affine := fun _ =>
        ⟨aff_alpha_mem fm ⟨CharPModel.jBar N, fm.jBar_mem⟩, aff_alpha_mem fm ⟨CharPModel.jNBar N, fm.jNBar_mem⟩,
          aff_beta_mem fm ⟨CharPModel.jBar N, fm.jBar_mem⟩, aff_beta_mem fm ⟨CharPModel.jNBar N, fm.jNBar_mem⟩⟩
      gens_cusp := fun hcusp => absurd hvaff hcusp
      const_mem := aff_const_mem fm
      nIncl := fun φ hφ hreg => aff_nIncl R fm hred dataAll hsep hP hqN hBFC v hvaff.1 hint φ hφ hreg
      valueLaw := fun s hs W hW hWv => (hgood s hs).choose_spec.2.1 W hW hWv
      separates := fun W hWs hW => aff_separates R fm hred dataAll hsep hP hqN v hvaff hint W hWs hW
      etale := aff_etale R fm hred dataAll hsep hP hqN hBFC v hv hvaff
      dichotomy := fun W hW => aff_dichotomy v hv W hW
      regularOver := fun s hs W hW => (hgood s hs).choose_spec.2.2 W hW }⟩

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace.ModularCurve.ChartGen"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (hBFC : ∀ s : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N),
      (∃ p : Polynomial (CharPModel.affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (CharPModel.affineBaseFin N A).subtype s p = 0) → s ∈ fm.BFin) :
    ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      IsAffineGeomPlace k N v →
      ∃ S : Set (modularFunctionFieldBar (N * q)), IsChartAt R v S :=
  ModularCurve.PlaceSpecialization.exists_isChartAt_affine R fm hred dataAll hsep hP hqN hBFC

end S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_isChartAt_of_isAffineGeomPlace (solution)
