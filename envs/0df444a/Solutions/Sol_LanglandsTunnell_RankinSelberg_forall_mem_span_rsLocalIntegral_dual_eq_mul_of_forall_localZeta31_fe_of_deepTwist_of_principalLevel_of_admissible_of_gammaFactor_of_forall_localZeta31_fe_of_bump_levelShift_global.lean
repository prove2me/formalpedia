-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/15485b33-bf99-5a22-8331-0725dd7d4e8d

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one
import Theorems.Thm_LanglandsTunnell_clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_forall_eval_mul_eval_mul_cpow_eq_of_clearedFE_of_clearedFE_of_ne_zero
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_twist_coefficientFn_principalSeries3_congruenceK1_invariant_iotaGL_bump_of_pos_of_level
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_principalSeries3_whittaker_deepTwist_centralChar_of_higherUnitsAt_unitary_shallow
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_principalSeries3
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_cleared_fe_of_laurent_fe_of_rational_forms
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_eq_laurent_of_deepTwist_of_principalLevel_of_admissible
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_of_forall_rsLocalIntegral_clearedFE_of_centralChar_eq_of_deepTwist_pairStability32_of_bump
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_principalSeries3_of_forall_torusZeta_fe_multiplicativity3_ed3
import Theorems.Thm_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SpectralSide.instCompactSpaceMatrix LocalGL2.Kirillov.fintype_Qm LocalGL2.Kirillov.fintype_Ch LocalGL2.Kirillov.addCommGroup_Ch LocalGL2.Kirillov.finite_Qm LocalGL2.Kirillov.addCommGroup_additive_Qm LocalGL2.Kirillov.decidableEq_Ch LocalGL2.Kirillov.finite_additive_Qm IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion"
p2m_attr_erase "simp" "FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.mem_sigmaCentralizer_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one"
p2m_attr_erase "simp" "LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply LanglandsTunnell.CubicInduction.fnTwist3_apply LocalGL2.Kirillov.zG_coe LocalGL2.Kirillov.wG_coe LocalGL2.Kirillov.dg_coe LocalGL2.Kirillov.rT_apply LocalGL2.Kirillov.rT_one Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

theorem W1p_G3_monomial (Nc : ℂ) (hNc : Nc ≠ 0) (C0 C1 : ℂ) (k0 k1 : ℤ) (s : ℂ) :
    (C0 * Nc ^ ((k0 : ℂ) * (-s))) * (C1 * Nc ^ ((k1 : ℂ) * (-s))) =
      (Polynomial.C (C0 * C1)).eval (Nc ^ s) * Nc ^ (((-(k0 + k1) : ℤ) : ℂ) * s) := by
  rw [Polynomial.eval_C,
    show ((-(k0 + k1) : ℤ) : ℂ) * s = (k0 : ℂ) * (-s) + (k1 : ℂ) * (-s) by push_cast; ring,
    Complex.cpow_add _ _ hNc]
  ring

theorem W1p_G2_monomial (Nc : ℂ) (hNc : Nc ≠ 0) (ε1 ε2 : ℂ) (a : ℕ) (s : ℂ) :
    (ε1 * (Nc ^ ((1 : ℂ) / 2 - s)) ^ a) * (ε2 * (Nc ^ ((1 : ℂ) / 2 - s)) ^ a) =
      (ε1 * ε2 * Nc ^ a) * Nc ^ (((-2 * (a : ℤ) : ℤ) : ℂ) * s) := by
  have key : (Nc ^ ((1 : ℂ) / 2 - s)) ^ a * (Nc ^ ((1 : ℂ) / 2 - s)) ^ a =
      Nc ^ a * Nc ^ (((-2 * (a : ℤ) : ℤ) : ℂ) * s) := by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hNc, ← Complex.cpow_natCast,
      ← Complex.cpow_add _ _ hNc]
    congr 1
    push_cast
    ring
  calc _ = ε1 * ε2 * ((Nc ^ ((1 : ℂ) / 2 - s)) ^ a * (Nc ^ ((1 : ℂ) / 2 - s)) ^ a) := by ring
    _ = _ := by rw [key]; ring

theorem W1p_G1_centralChar_higherUnitsAt
    (p : HeightOneSpectrum (𝓞 ℚ)) (W₃base : LocalGL3 p → ℂ)
    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (d : ℕ)
    (hπ₀lev : ∃ W' ∈ gl3CyclicSubspace W₃base, W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        ∀ g : LocalGL3 p,
          ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g) :
    ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (ω₃ * (χ ^ 3)⁻¹) u = 1 := by
  intro u hu
  obtain ⟨W', hW'mem, hW'ne, hW'inv⟩ := hπ₀lev
  obtain ⟨hval, hball⟩ := hu

  have hcent : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W' (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W' h := by
    refine Submodule.span_induction
      (p := fun (f : LocalGL3 p → ℂ) _ => ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
        f (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * f h) ?_ ?_ ?_ ?_ hW'mem
    · rintro _ ⟨h₀, rfl⟩ t h
      simp only [gl3AmbientRightTranslate_apply, mul_assoc]
      exact hω₃ t (h * h₀)
    · intro t h
      simp
    · intro f₁ f₂ _ _ h₁ h₂ t h
      simp only [Pi.add_apply, h₁, h₂, mul_add]
    · intro c f _ hf t h
      simp only [Pi.smul_apply, hf, smul_eq_mul]
      ring

  set k : LocalGL3 p := Matrix.GeneralLinearGroup.scalar (Fin 3) u with hk
  have hkval : ∀ (t : (p.adicCompletion ℚ)ˣ),
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) t : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
        Matrix.diagonal (fun _ => (t : p.adicCompletion ℚ)) := by
    intro t
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]
  have hval' : Valued.v ((u⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  have hkK : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
    rw [mem_localMaximalCompact3_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [hk, hkval]
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq, hval]
      · rw [Matrix.diagonal_apply_ne _ hij, map_zero]; exact zero_le'
    · rw [hk, ← map_inv, hkval]
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq, hval']
      · rw [Matrix.diagonal_apply_ne _ hij, map_zero]; exact zero_le'
  have hkd : ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ)) := by
    intro i j
    rw [hk, hkval]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rcases hball with hd0 | hle
      · subst hd0
        simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero]
        refine le_trans (Valuation.map_sub _ _ _) (max_le (le_of_eq hval) (le_of_eq (map_one _)))
      · exact hle
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero, map_zero]
      exact zero_le'

  have hcomm : ∀ g : LocalGL3 p, g * k = k * g := by
    intro g
    rw [hk]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hkval]
    rw [← Matrix.scalar_apply]
    exact ((Matrix.scalar_commute (u : p.adicCompletion ℚ) (fun r' => Commute.all _ _) _).eq).symm
  have hdet : Matrix.GeneralLinearGroup.det k = u ^ 3 := by
    rw [hk]; ext; simp

  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : LocalGL3 p, W' g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hW'ne (funext h)
  have h1 := hW'inv k hkK hkd g₀
  rw [hcomm, map_mul, map_mul, hdet, Units.val_mul] at h1
  rw [hk, hcent] at h1
  have hχne : ((χ (Matrix.GeneralLinearGroup.det g₀) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hχu3 : ((χ (u ^ 3) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h3 : (((χ (u ^ 3) : ℂˣ) : ℂ)⁻¹ * ((ω₃ u : ℂˣ) : ℂ)) *
      ((((χ (Matrix.GeneralLinearGroup.det g₀)) : ℂˣ) : ℂ)⁻¹ * W' g₀) =
      1 * ((((χ (Matrix.GeneralLinearGroup.det g₀)) : ℂˣ) : ℂ)⁻¹ * W' g₀) := by
    rw [one_mul]
    calc (((χ (u ^ 3) : ℂˣ) : ℂ)⁻¹ * ((ω₃ u : ℂˣ) : ℂ)) *
          ((((χ (Matrix.GeneralLinearGroup.det g₀)) : ℂˣ) : ℂ)⁻¹ * W' g₀) =
          (((χ (u ^ 3) : ℂˣ) : ℂ) * (((χ (Matrix.GeneralLinearGroup.det g₀)) : ℂˣ) : ℂ))⁻¹ *
            (((ω₃ u : ℂˣ) : ℂ) * W' g₀) := by ring
      _ = _ := h1
  have h4 := mul_right_cancel₀ (mul_ne_zero (inv_ne_zero hχne) hg₀) h3
  have h2 : ((ω₃ u : ℂˣ) : ℂ) = ((χ (u ^ 3) : ℂˣ) : ℂ) := by
    calc ((ω₃ u : ℂˣ) : ℂ) = ((χ (u ^ 3) : ℂˣ) : ℂ) * (((χ (u ^ 3) : ℂˣ) : ℂ)⁻¹ * ((ω₃ u : ℂˣ) : ℂ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hχu3, one_mul]
      _ = ((χ (u ^ 3) : ℂˣ) : ℂ) := by rw [h4, mul_one]
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, ← map_pow, mul_inv_eq_one]
  exact Units.val_injective h2

set_option maxHeartbeats 4000000 in
open scoped Classical in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)

    (ω₃ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hω₃u : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ω₃ x : ℂˣ) : ℂ)‖ = 1)
    (hω₃ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃base (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₃ t : ℂˣ) : ℂ) * W₃base h)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace W₃base,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (d : ℕ)
    (hπ₀lev : ∃ W' ∈ gl3CyclicSubspace W₃base, W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        ∀ g : LocalGL3 p,
          ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)

    (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hθ1 : θ 1 = 1)
    (hθu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((θ 0 z : ℂˣ) : ℂ)‖ = 1)
    (C : Fin 2 → ℂ) (k : Fin 2 → ℤ)
    (h31 : ∀ i : Fin 2,
      ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃base (θ i) g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base (θ i) s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) (θ i)⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base (θ i) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              (C i * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k i : ℂ) * s))))

    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))

    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ 0 z : ℂˣ) : ℂ) * w₂base g)

    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)

    (hcθ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, θ 0 u = 1)
    (hkC : 6 * (b + 3 * d + 3) + 7 ≤ kp)

    (Δ : ℕ) (hΔ : 6 * d + 18 + Δ ≤ kp)

    (hbumpAll : ∀ (ξA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ξA →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → NumberField.TateGlobal.IsUnramifiedCharAt ξA v) →
      (∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ ξA v 0 0) →
      ∀ B : ℕ, 2 * d + 6 ≤ B → LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ξA p) B →
      ∃ W₀ ∈ gl3CyclicSubspace (fun g : LocalGL3 p =>
          ((NumberField.TateGlobal.localChar ξA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W₃base g),
        (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p (3 * B + Δ), ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
        (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
        (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
          ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
        W₀ (iotaGL 1) = 1)

    (h31all : ∃ (Cst : ℂ) (yst : (p.adicCompletion ℚ)ˣ) (est : ℕ) (kst : ℤ),
      ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η cη → cη ≤ b →
      (∀ z : (p.adicCompletion ℚ)ˣ, ‖((η z : ℂˣ) : ℂ)‖ = 1) →
      ∀ g : LocalGL3 p,
        letI := localBorel ℚ p
        ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            W₃base η g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base η s g *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W₃base η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
              ((Cst * ((η yst : ℂˣ) : ℂ) ^ est) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((kst : ℂ) * s))))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))
    (hβ : ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W₃base (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 ∧
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])

    (hΓ :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W₃base,
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              R₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                (R₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((r : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),

          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧

          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) w₂ =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              ((C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) *
                (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s)))) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s))) := by

  classical

  have hN0 : Ideal.absNorm p.asIdeal ≠ 0 := fun h => p.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hN1' : Ideal.absNorm p.asIdeal ≠ 1 := fun h => p.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hN1 : 1 < Ideal.absNorm p.asIdeal := by omega
  have hNc : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hN0

  have hω₀ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (d + 1), (ω₃ * (χ ^ 3)⁻¹) u = 1 :=
    fun u hu => W1p_G1_centralChar_higherUnitsAt p W₃base ω₃ hω₃ χ d hπ₀lev u
      (LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p (Nat.le_succ d) hu)

  obtain ⟨lam, W2, hlamω, hlamcond, hlamu, hlam, hshallow, hmem, hW2law, hW2sm, hW2ne, hω2, hlev2⟩ :=
    LanglandsTunnell.RankinSelberg.exists_principalSeries3_whittaker_deepTwist_centralChar_of_higherUnitsAt_unitary_shallow
      p ω₃ hω₃u χ hχu kp hkp (d + 1) (Nat.succ_pos d) (by omega) hω₀

  obtain ⟨ξA, hadm, hcondA, hoffA, hinf⟩ :=
    LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
      {p} (fun _ => 2 * d + 6) (fun _ _ => by show 3 ≤ 2 * d + 6; omega)
  have hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ξA p) (2 * d + 6) :=
    hcondA p (Finset.mem_singleton_self p)
  have hoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → NumberField.TateGlobal.IsUnramifiedCharAt ξA v :=
    fun v hv => hoffA v (by simpa using hv)

  have hξu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((NumberField.TateGlobal.localChar ξA p x : ℂˣ) : ℂ)‖ = 1 :=
    fun x => by rw [NumberField.TateGlobal.localChar_apply]; exact hadm.2.2 _

  have hbump1 := hbumpAll ξA hadm hoff hinf (2 * d + 6) le_rfl hξB
  obtain ⟨W₀2, hW₀2mem, hW₀2K, hW₀2ι, hW₀2supp, hW₀2one⟩ :=
    LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_twist_coefficientFn_principalSeries3_congruenceK1_invariant_iotaGL_bump_of_pos_of_level
      p lam hlam hlamu W2 hmem hW2ne χ hχu (d + 1) (Nat.succ_pos d) hshallow hlev2 (NumberField.TateGlobal.localChar ξA p) hξu (2 * d + 6) hξB (by omega)

  have hW₀2K' : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p (3 * (2 * d + 6) + Δ), ∀ g : LocalGL3 p, W₀2 (g * k) = W₀2 g :=
    fun k hk g => hW₀2K k (LanglandsTunnell.CubicInduction.congruenceK1_antitone (𝓞 ℚ) ℚ p (Nat.le_add_right _ _) hk) g

  obtain ⟨wJ, hwJ⟩ : ∃ wJ : GL (Fin 2) (p.adicCompletion ℚ),
      (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two_of]), rfl⟩

  obtain ⟨E, e, hE, he⟩ : ∃ (E : Fin 3 → ℂ) (e : Fin 3 → ℤ),
      (E = fun i => LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (lam i * θ 0) *
          LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (lam i) * (Ideal.absNorm p.asIdeal : ℂ) ^ kp) ∧
      (e = fun _ => -2 * (kp : ℤ)) := ⟨_, _, rfl, rfl⟩

  have key : ∀ (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwne : w ≠ 0)
    (hwirr : ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
      w' ≠ 0 → w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w' (g * h)))
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hwcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ 0 z : ℂˣ) : ℂ) * w g)
    (hwrat :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W₃base,
          ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))))
    (hwΓ :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W₃base,
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              R₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                (R₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((r : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))))
    ,
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace W₃base,
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              (1 : Polynomial ℂ).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C (((θ 0 (-1) : ℂˣ) : ℂ) * (E 0 * E 1 * E 2))).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(e 0 + e 1 + e 2) : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
    intro w hwlaw hwK hwne hwirr hwadm hwcentral hwrat hwΓ

    have hwKb := LanglandsTunnell.RankinSelberg.forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
      p N w hwK b hNb

    have h751 := fun (i : Fin 3) =>
      AutomorphicForm.WhittakerModel.exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one
        p w hwlaw b (fun k hk g => hwKb k g hk) hwne hwirr hwadm (θ 0) hwcentral (hθu _) (lam i) kp (hlamcond i)
        (hlamu i _) (by omega) wJ hwJ

    have hFE₂ :=
      LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_principalSeries3_of_forall_torusZeta_fe_multiplicativity3_ed3
        p lam ω₃ hlamω hlam W2 hmem hW2law hW2sm hω2 (θ 0) N _hN w hwlaw hwK hwne hwirr hwadm hwcentral w₀p hw₀p wJ hwJ E e
        (fun w' hw' => by
          obtain ⟨P, Pd, m, md, σ₀, σ₁, c1, z1, c2, z2, -, fe⟩ := h751 0 w' hw'
          refine ⟨P, Pd, m, md, σ₀, σ₁, c1, z1, c2, z2, fun s => ?_⟩
          rw [fe s]; simp only [hE, he]; rw [W1p_G2_monomial _ hNc])
        (fun w' hw' => by
          obtain ⟨P, Pd, m, md, σ₀, σ₁, c1, z1, c2, z2, -, fe⟩ := h751 1 w' hw'
          refine ⟨P, Pd, m, md, σ₀, σ₁, c1, z1, c2, z2, fun s => ?_⟩
          rw [fe s]; simp only [hE, he]; rw [W1p_G2_monomial _ hNc])
        (fun w' hw' => by
          obtain ⟨P, Pd, m, md, σ₀, σ₁, c1, z1, c2, z2, -, fe⟩ := h751 2 w' hw'
          refine ⟨P, Pd, m, md, σ₀, σ₁, c1, z1, c2, z2, fun s => ?_⟩
          rw [fe s]; simp only [hE, he]; rw [W1p_G2_monomial _ hNc])

    have hrat2 :=
      LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_principalSeries3
        p lam ω₃ hlamω hlam hlamu W2 hmem hW2law hW2sm hω2 (θ 0) N _hN w hwlaw hwK hwne hwirr hwadm hwcentral w₀p hw₀p

    exact
      LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_of_forall_rsLocalIntegral_clearedFE_of_centralChar_eq_of_deepTwist_pairStability32_of_bump
        p ω₃ hω₃u χ hχu kp hkp (NumberField.TateGlobal.localChar ξA p) hξu (2 * d + 6) hξB (3 * (2 * d + 6) + Δ) W₃base hW₃law hW₃sm hω₃ d hπ₀lev
        W2 hW2law hW2sm hω2 (d + 1) hlev2 (θ 0) hθu b hcθ N _hN hNb w hwlaw hwK hwne hwirr hwadm hwcentral w₀p hw₀p
        (by rw [show max d (d + 1) = d + 1 from max_eq_right (Nat.le_succ d)]; omega) (by omega) (by omega)
        (by rw [show max d (d + 1) = d + 1 from max_eq_right (Nat.le_succ d)]; omega) (by omega)
        hbump1 ⟨W₀2, hW₀2mem, hW₀2K', hW₀2ι, hW₀2supp, hW₀2one⟩ hwrat hrat2 hwΓ _ _ _ one_ne_zero hFE₂

  have hLV :=
    LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_eq_laurent_of_deepTwist_of_principalLevel_of_admissible
      p W₃base hW₃law hW₃sm hW₃ne ω₃ hω₃ hW₃irr hW₃adm hWgauge χ hχu kp hkp d hπ₀lev θ hθ1 hθu C k h31 N _hN
      w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral b hNb hcθ hkC hπ hϖ hw₂gr hβ w₀p hw₀p

  have keyV := key w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral
    (fun μ₂ _ μN₂ _ w₂ hw₂ W₃ hW₃ => by
      obtain ⟨P, Pd, m, md, σ₂, σ₃, c1, c2, L1, L2⟩ := hLV μ₂ μN₂ w₂ hw₂ W₃ hW₃
      exact ⟨P, Pd, 1, 1, m, md, σ₂, σ₃, one_ne_zero, one_ne_zero, c1, c2,
        fun s hs => by rw [Polynomial.eval_one, mul_one]; exact L1 s hs,
        fun s hs => by rw [Polynomial.eval_one, mul_one]; exact L2 s hs⟩)
    hΓ

  have hθu' : ∀ (i : Fin 2) (z : (p.adicCompletion ℚ)ˣ), ‖((θ i z : ℂˣ) : ℂ)‖ = 1 := by
    intro i z
    fin_cases i
    · exact hθu z
    · simp [hθ1]
  have hcθ' : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p ((![b, 0] : Fin 2 → ℕ) i), θ i u = 1 := by
    intro i u hu
    fin_cases i
    · exact hcθ u (by simpa using hu)
    · simp [hθ1]
  obtain ⟨wr, hrlaw, hrK, hrne, hr1, hrirr, hradm, hrcentral', hrPS, hrgr⟩ :=
    LanglandsTunnell.CubicInduction.exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt
      p θ hθu' ![b, 0] hcθ' N _hN b hNb (by simp) hπ hϖ
  have hrcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      wr (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ 0 z : ℂˣ) : ℂ) * wr g := by
    intro z g
    rw [hrcentral' z g, hθ1, MonoidHom.one_apply, mul_one]

  have hC :=
    LanglandsTunnell.RankinSelberg.forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_principalSeries2
      p W₃base hW₃law hW₃sm hW₃ne ω₃ hω₃ hW₃irr hWgauge θ (fun _ => b)
      (fun i u hu => by
        fin_cases i
        · exact hcθ u hu
        · simp [hθ1])
      C k h31 N _hN wr hrlaw hrK hrne hrirr hrPS b hNb hπ hϖ hrgr hβ w₀p hw₀p

  have keyR := key wr hrlaw hrK hrne hrirr hradm hrcentral
    (fun μ₂ _ μN₂ _ w₂ hw₂ W₃ hW₃ => by
      obtain ⟨P, Pd, m, md, σ₂, σ₃, c1, c2, L1, L2, -⟩ := hC μ₂ μN₂ w₂ hw₂ W₃ hW₃
      exact ⟨P, Pd, 1, 1, m, md, σ₂, σ₃, one_ne_zero, one_ne_zero, c1, c2,
        fun s hs => by rw [Polynomial.eval_one, mul_one]; exact L1 s hs,
        fun s hs => by rw [Polynomial.eval_one, mul_one]; exact L2 s hs⟩)
    ⟨Polynomial.C (C 0 * C 1), 1, -(k 0 + k 1), one_ne_zero,
      fun μ₂ _ μN₂ _ w₂ hw₂ W₃ hW₃ P Pd Q Qd m md σ₂ σ₃ hQ hQd c1 c2 r1 r2 s => by
        obtain ⟨P₀, Pd₀, m₀, md₀, σa, σb, -, -, La, Lb, FE₀⟩ := hC μ₂ μN₂ w₂ hw₂ W₃ hW₃
        letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
        haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
        have h870 := LanglandsTunnell.RankinSelberg.forall_cleared_fe_of_laurent_fe_of_rational_forms
          (Ideal.absNorm p.asIdeal) hN1
          (fun s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) w₂)
          (fun s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)))
          (fun s => (C 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 0 : ℂ) * (-s))) *
                (C 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k 1 : ℂ) * (-s))))
          P₀ Pd₀ m₀ md₀ σa σb La Lb FE₀ P Pd Q Qd m md σ₂ σ₃ hQ hQd r1 r2 s
        rw [Polynomial.eval_one, one_mul, ← W1p_G3_monomial _ hNc]
        exact h870⟩

  intro μ₂ _ μN₂ _ w₂ hw₂ W₃ hW₃

  obtain ⟨Wb, hWbmem, c, hc, hWb⟩ :=
    LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite
      p W₃base hW₃law hW₃sm hW₃ne hW₃irr hW₃adm 1 (Finset.univ : Finset Unit) (fun _ => wr)
      (fun _ _ => hrlaw)
      (fun _ _ => ⟨AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N,
        (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N _hN).2, hrK⟩) μ₂ μN₂
  have hwr_mem : wr ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => wr (g * h)) :=
    Submodule.subset_span ⟨1, funext fun g => by simp⟩
  obtain ⟨P₀, Pd₀, m₀, md₀, σa, σb, ca, cb, La, Lb, FE₀⟩ := hC μ₂ μN₂ wr hwr_mem Wb hWbmem
  have hP₀ : P₀ ≠ 0 := by
    intro hP
    have hs : σa < (((σa + 1 : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]; linarith
    have h1 := La ((σa + 1 : ℝ) : ℂ) hs
    have h2 := (hWb () (Finset.mem_univ _) ((σa + 1 : ℝ) : ℂ)).2
    rw [hP, Polynomial.eval_zero, mul_zero] at h1
    have hdet1 : ((Matrix.GeneralLinearGroup.det (1 : GL (Fin 2) (p.adicCompletion ℚ)) :
        (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by simp
    have hmod : (LanglandsTunnell.TateLocal.modulus (1 : p.adicCompletion ℚ) : ℝ) = 1 := by
      simp [LanglandsTunnell.TateLocal.modulus]
    simp only [hdet1, hmod, Complex.ofReal_one, Complex.one_cpow, mul_one] at h2
    rw [h1] at h2
    exact (mul_ne_zero hc hr1) h2.symm

  have hΓeq :=
    LanglandsTunnell.forall_eval_mul_eval_mul_cpow_eq_of_clearedFE_of_clearedFE_of_ne_zero
      (Ideal.absNorm p.asIdeal) hN1
      (Polynomial.C (((θ 0 (-1) : ℂˣ) : ℂ) * (E 0 * E 1 * E 2))) 1 (Polynomial.C (C 0 * C 1)) 1
      (-(e 0 + e 1 + e 2)) (-(k 0 + k 1)) P₀ Pd₀ 1 1 m₀ md₀ hP₀ one_ne_zero
      (keyR μ₂ μN₂ wr hwr_mem Wb hWbmem P₀ Pd₀ 1 1 m₀ md₀ σa σb one_ne_zero one_ne_zero ca cb
        (fun s hs => by rw [Polynomial.eval_one, mul_one]; exact La s hs)
        (fun s hs => by rw [Polynomial.eval_one, mul_one]; exact Lb s hs))
      (fun s => by
        simp only [Polynomial.eval_one, one_mul, mul_one]
        rw [← W1p_G3_monomial _ hNc]
        exact FE₀ s)

  obtain ⟨P, Pd, m, md, σ₂, σ₃, c1, c2, L1, L2⟩ := hLV μ₂ μN₂ w₂ hw₂ W₃ hW₃
  have hFA := keyV μ₂ μN₂ w₂ hw₂ W₃ hW₃ P Pd 1 1 m md σ₂ σ₃ one_ne_zero one_ne_zero c1 c2
    (fun s hs => by rw [Polynomial.eval_one, mul_one]; exact L1 s hs)
    (fun s hs => by rw [Polynomial.eval_one, mul_one]; exact L2 s hs)
  have hFB := LanglandsTunnell.clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq
    (Ideal.absNorm p.asIdeal) hN1
    (Polynomial.C (((θ 0 (-1) : ℂˣ) : ℂ) * (E 0 * E 1 * E 2))) 1 (Polynomial.C (C 0 * C 1)) 1
    (-(e 0 + e 1 + e 2)) (-(k 0 + k 1)) one_ne_zero hΓeq P Pd 1 1 m md hFA
  refine ⟨P, Pd, m, md, σ₂, σ₃, c1, c2, L1, L2, fun s => ?_⟩
  have h := hFB s
  simp only [Polynomial.eval_one, one_mul, mul_one] at h
  rw [← W1p_G3_monomial _ hNc] at h
  exact h

end S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_span_rsLocalIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_deepTwist_of_principalLevel_of_admissible_of_gammaFactor_of_forall_localZeta31_fe_of_bump_levelShift_global (solution)
