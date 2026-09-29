-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/546e2143-61db-5f7b-a697-f6c3964820b2

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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_twistFamily_eq_finsum_and_forall_le_jacquetTruncated3_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_cellSectionOf_twistFamily_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_of_forall_isGL3PsiWhittakerFn_finsum_cpow_mul
import Theorems.Thm_LanglandsTunnell_eq_of_forall_finsum_cpow_neg_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval
import Theorems.Thm_LanglandsTunnell_forall_cpow_mul_eval_eq_of_forall_lt_re
import Theorems.Thm_LanglandsTunnell_clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.mem_sigmaCentralizer_iff"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical Topology

namespace M2PGlue

theorem exists_real_forall_norm_apply_eq_norm_rpow (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ c : ℝ, ∀ a : (p.adicCompletion ℚ)ˣ, ‖((χ a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ c := by
  obtain ⟨n, hn⟩ :=
    LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ p χ hχ.continuous
  obtain ⟨η, σ, hη, -, hχη⟩ :=
    LanglandsTunnell.TateLocal.exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt ℚ p χ n hn
  refine ⟨σ, fun a => ?_⟩
  have hmod : ((modulus (a : p.adicCompletion ℚ) : ℝ)) = ‖(a : p.adicCompletion ℚ)‖ := by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl
  have hpos : 0 < ‖(a : p.adicCompletion ℚ)‖ := norm_pos_iff.mpr a.ne_zero
  rw [hχη a, norm_mul, hη a, one_mul, hmod, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
    Complex.ofReal_re]

noncomputable def normPow (p : HeightOneSpectrum (𝓞 ℚ)) (u : ℂ) : (p.adicCompletion ℚ)ˣ →* ℂˣ where
  toFun a := Units.mk0 (((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (by exact_mod_cast (norm_ne_zero_iff.mpr a.ne_zero)))
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Units.val_mul, norm_mul, Complex.ofReal_mul, Units.val_mk0]
    exact Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _) u

@[scoped simp] theorem normPow_apply (p : HeightOneSpectrum (𝓞 ℚ)) (u : ℂ) (a : (p.adicCompletion ℚ)ˣ) :
    ((normPow p u a : ℂˣ) : ℂ) = ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u := rfl

theorem normPow_zero (p : HeightOneSpectrum (𝓞 ℚ)) : normPow p 0 = 1 := by
  ext a; simp

theorem eventually_norm_eq (p : HeightOneSpectrum (𝓞 ℚ)) (x : (p.adicCompletion ℚ)ˣ) :
    ∀ᶠ y : (p.adicCompletion ℚ)ˣ in 𝓝 x, ‖(y : p.adicCompletion ℚ)‖ = ‖(x : p.adicCompletion ℚ)‖ := by
  have h0 : (Valued.v (x : p.adicCompletion ℚ)) ≠ 0 := by simp
  have h1 : ∀ᶠ z in 𝓝 (x : p.adicCompletion ℚ), ‖z‖ = ‖(x : p.adicCompletion ℚ)‖ :=
    Filter.mem_of_superset (Valued.locally_const h0) (fun z hz => by
      simp only [Set.mem_setOf_eq] at hz
      show ‖z‖ = ‖(x : p.adicCompletion ℚ)‖
      rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hz])
  exact (Units.continuous_val.tendsto x).eventually h1

theorem isLocallyConstant_normPow (p : HeightOneSpectrum (𝓞 ℚ)) (u : ℂ) :
    IsLocallyConstant (normPow p u) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  exact (eventually_norm_eq p x).mono (fun y hy => Units.ext (by simp [hy]))

theorem exists_twistFamily (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i)) :
    ∃ lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ),
      lamU 0 = lam ∧
      (∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
        ((lamU u 0 a : ℂˣ) : ℂ) = ((lam 0 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u ∧
          ((lamU u 1 a : ℂˣ) : ℂ) = ((lam 1 a : ℂˣ) : ℂ) ∧
            ((lamU u 2 a : ℂˣ) : ℂ) = ((lam 2 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ (-u)) ∧
      (∀ (u : ℂ) (i : Fin 3), IsLocallyConstant (lamU u i)) := by
  refine ⟨fun u => ![lam 0 * normPow p u, lam 1, lam 2 * normPow p (-u)], ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> ext a <;> simp
  · intro u a
    simp
  · intro u i
    have hmul : ∀ (f g : (p.adicCompletion ℚ)ˣ →* ℂˣ), IsLocallyConstant f → IsLocallyConstant g →
        IsLocallyConstant (f * g) := fun f g hf hg => by
      have : ⇑(f * g) = ⇑f * ⇑g := rfl
      rw [this]; exact hf.mul hg
    fin_cases i
    · simpa using hmul _ _ (hlam 0) (isLocallyConstant_normPow p u)
    · simpa using hlam 1
    · simpa using hmul _ _ (hlam 2) (isLocallyConstant_normPow p (-u))

theorem exists_forall_chamber_of_twistFamily (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u 0 a : ℂˣ) : ℂ) = ((lam 0 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u ∧
        ((lamU u 1 a : ℂˣ) : ℂ) = ((lam 1 a : ℂˣ) : ℂ) ∧
          ((lamU u 2 a : ℂˣ) : ℂ) = ((lam 2 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ (-u)) :
    ∃ u₀ : ℝ, ∀ u : ℂ, u₀ < u.re →
      ∃ σ : Fin 3 → ℝ,
        (∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
          ‖((lamU u i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i)) ∧
        σ 1 < σ 0 ∧ σ 2 < σ 1 := by
  choose c hc using fun i => exists_real_forall_norm_apply_eq_norm_rpow p (lam i) (hlam i)
  refine ⟨max (c 1 - c 0) (c 2 - c 1), fun u hu => ⟨![c 0 + u.re, c 1, c 2 - u.re], ?_, ?_, ?_⟩⟩
  · intro i a
    have hpos : 0 < ‖(a : p.adicCompletion ℚ)‖ := norm_pos_iff.mpr a.ne_zero
    obtain ⟨h0, h1, h2⟩ := hlamU u a
    fin_cases i
    · show ‖((lamU u 0 a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (c 0 + u.re)
      rw [h0, norm_mul, hc 0 a, Complex.norm_cpow_eq_rpow_re_of_pos hpos, ← Real.rpow_add hpos]
    · show ‖((lamU u 1 a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (c 1)
      rw [h1, hc 1 a]
    · show ‖((lamU u 2 a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (c 2 - u.re)
      rw [h2, norm_mul, hc 2 a, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re,
        ← Real.rpow_add hpos, sub_eq_add_neg]
  · have := (le_max_left (c 1 - c 0) (c 2 - c 1)).trans_lt hu
    show c 1 < c 0 + u.re
    linarith
  · have := (le_max_right (c 1 - c 0) (c 2 - c 1)).trans_lt hu
    show c 2 - u.re < c 1
    linarith

theorem shift_eval (N : ℂ) (hN : N ≠ 0) (Q : Polynomial ℂ) (k : ℤ) (s u : ℂ) :
    N ^ ((k : ℂ) * s) * (Polynomial.C (N ^ ((k : ℂ) * u)) * Q.comp (Polynomial.C (N ^ (-u)) * Polynomial.X)).eval
        (N ^ (-s)) = N ^ ((k : ℂ) * (s + u)) * Q.eval (N ^ (-(s + u))) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X]
  rw [mul_add, Complex.cpow_add _ _ hN, show -(s + u) = -u + -s by ring, Complex.cpow_add _ _ hN]
  ring

theorem hfe_shift (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (wJ : GL (Fin 2) (p.adicCompletion ℚ))
    (χ χ' : (p.adicCompletion ℚ)ˣ →* ℂˣ) (u : ℂ)
    (hχ' : ∀ y : (p.adicCompletion ℚ)ˣ, ((χ' y : ℂˣ) : ℂ) = ((χ y : ℂˣ) : ℂ) * ((‖(y : p.adicCompletion ℚ)‖ : ℂ)) ^ u)
    (E₀ : ℂ) (e₀ : ℤ)
    (h : letI := localBorel ℚ p
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))))) :
    letI := localBorel ℚ p
    ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ' y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ' y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ' y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ' y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * u) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) := by
  obtain ⟨P, Pd, m, md, σ₀, σ₁, h1, h2, h3, h4, h5⟩ := h
  have hN : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fun h => p.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hmod : ∀ y : (p.adicCompletion ℚ)ˣ, ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) = ((‖(y : p.adicCompletion ℚ)‖ : ℂ)) := by
    intro y
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl
  have hn : ∀ y : (p.adicCompletion ℚ)ˣ, ((‖(y : p.adicCompletion ℚ)‖ : ℂ)) ≠ 0 := fun y => by
    exact_mod_cast (norm_ne_zero_iff.mpr y.ne_zero)
  have hint1 : ∀ (s : ℂ) (y : (p.adicCompletion ℚ)ˣ),
      w (diagOne y) * ((χ' y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) =
        w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((s + u) - 1 / 2) := by
    intro s y
    rw [hχ', hmod, show s + u - 1 / 2 = u + (s - 1 / 2) by ring, Complex.cpow_add _ _ (hn y)]
    ring
  have hint2 : ∀ (s : ℂ) (y : (p.adicCompletion ℚ)ˣ),
      w (diagOne y * wJ) * (((χ' y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) =
        w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - (s + u)) := by
    intro s y
    rw [hχ', hmod, mul_inv, show 1 / 2 - (s + u) = -u + (1 / 2 - s) by ring, Complex.cpow_add _ _ (hn y),
      Complex.cpow_neg]
    ring
  have hre : ∀ s : ℂ, (s + u).re = s.re + u.re := fun s => by simp
  refine ⟨Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * u)) *
      P.comp (Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ (-u)) * Polynomial.X),
    Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * u)) *
      Pd.comp (Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ (-u)) * Polynomial.X),
    m, md, σ₀ - u.re, σ₁ - u.re, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    simp_rw [hint1 s]
    exact h1 (s + u) (by rw [hre]; linarith)
  · intro s hs
    simp_rw [hint1 s]
    rw [h2 (s + u) (by rw [hre]; linarith), shift_eval _ hN]
  · intro s hs
    simp_rw [hint2 s]
    exact h3 (s + u) (by rw [hre]; linarith)
  · intro s hs
    simp_rw [hint2 s]
    rw [h4 (s + u) (by rw [hre]; linarith), shift_eval _ hN]
  · intro s
    rw [shift_eval _ hN, mul_assoc (E₀ * _), shift_eval _ hN, h5 (s + u), mul_add,
      Complex.cpow_add _ _ hN]
    ring

theorem evev (P : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    (P.eval (Polynomial.C y)).eval x = (P.map (Polynomial.evalRingHom x)).eval y := by
  have h := Polynomial.eval₂_at_apply (p := P) (Polynomial.evalRingHom x) (Polynomial.C y)
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at h
  rw [Polynomial.eval_map, h]

theorem s_continuation (N : ℕ) (hN : 1 < N) (P Q' P' Q : Polynomial ℂ) (m m' : ℤ) (c : ℝ)
    (h : ∀ s : ℂ, c < s.re →
      (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)) =
        (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)) =
        (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)) := by
  have key := LanglandsTunnell.forall_cpow_mul_eval_eq_of_forall_lt_re N hN (P * Q') (P' * Q) m m' c
    (fun u hu => by simpa only [Polynomial.eval_mul, mul_assoc] using h u hu)
  intro s
  simpa only [Polynomial.eval_mul, mul_assoc] using key s

theorem u_continuation (N : ℕ) (hN : 1 < N) (K E₀ E₁ E₂ : ℂ) (e₀ e₁ e₂ r : ℤ)
    (P₂ Pd₂ Q₂ Qd₂ : Polynomial (Polynomial ℂ)) (m₂ md₂ j jd : ℤ) (c : ℝ)
    (h : ∀ u : ℂ, c < u.re → ∀ s : ℂ,
        (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) *
          ((N : ℂ) ^ ((md₂ : ℂ) * s) * (Polynomial.C ((N : ℂ) ^ ((jd : ℂ) * u)) * Pd₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ (-s))) *
          (Q₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ s) =
        ((Polynomial.C (K * (E₀ * (N : ℂ) ^ ((e₀ : ℂ) * u) * (E₁ * (N : ℂ) ^ ((e₁ : ℂ) * 0)) * (E₂ * (N : ℂ) ^ ((e₂ : ℂ) * (-u)))))).eval ((N : ℂ) ^ s) *
            (N : ℂ) ^ ((r : ℂ) * s)) *
          ((N : ℂ) ^ ((m₂ : ℂ) * (-s)) * (Polynomial.C ((N : ℂ) ^ ((j : ℂ) * u)) * P₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ s)) *
          (Qd₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md₂ : ℂ) * s) * (Pd₂.eval 1).eval ((N : ℂ) ^ (-s))) *
          (Q₂.eval 1).eval ((N : ℂ) ^ s) =
        ((Polynomial.C (K * (E₀ * E₁ * E₂))).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
          ((N : ℂ) ^ ((m₂ : ℂ) * (-s)) * (P₂.eval 1).eval ((N : ℂ) ^ s)) * (Qd₂.eval 1).eval ((N : ℂ) ^ (-s)) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  intro s

  have keyL : ∀ u : ℂ,
      (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) *
          ((N : ℂ) ^ ((md₂ : ℂ) * s) * (Polynomial.C ((N : ℂ) ^ ((jd : ℂ) * u)) * Pd₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ (-s))) *
          (Q₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ s) =
        (N : ℂ) ^ ((jd : ℂ) * u) *
          (Polynomial.C ((N : ℂ) ^ ((md₂ : ℂ) * s)) * Pd₂.map (Polynomial.evalRingHom ((N : ℂ) ^ (-s))) *
            Q₂.map (Polynomial.evalRingHom ((N : ℂ) ^ s))).eval ((N : ℂ) ^ (-u)) := by
    intro u
    simp only [Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, evev]
    ring
  have keyR : ∀ u : ℂ,
      ((Polynomial.C (K * (E₀ * (N : ℂ) ^ ((e₀ : ℂ) * u) * (E₁ * (N : ℂ) ^ ((e₁ : ℂ) * 0)) * (E₂ * (N : ℂ) ^ ((e₂ : ℂ) * (-u)))))).eval ((N : ℂ) ^ s) *
            (N : ℂ) ^ ((r : ℂ) * s)) *
          ((N : ℂ) ^ ((m₂ : ℂ) * (-s)) * (Polynomial.C ((N : ℂ) ^ ((j : ℂ) * u)) * P₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ s)) *
          (Qd₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ (-s)) =
        (N : ℂ) ^ (((j + e₀ - e₂ : ℤ) : ℂ) * u) *
          (Polynomial.C (K * (E₀ * E₁ * E₂) * (N : ℂ) ^ ((r : ℂ) * s) * (N : ℂ) ^ ((m₂ : ℂ) * (-s))) *
            P₂.map (Polynomial.evalRingHom ((N : ℂ) ^ s)) * Qd₂.map (Polynomial.evalRingHom ((N : ℂ) ^ (-s)))).eval ((N : ℂ) ^ (-u)) := by
    intro u
    simp only [Polynomial.eval_mul, Polynomial.eval_C, evev, mul_zero, Complex.cpow_zero, mul_one]
    rw [show (((j + e₀ - e₂ : ℤ)) : ℂ) * u = (j : ℂ) * u + ((e₀ : ℂ) * u + (e₂ : ℂ) * (-u)) by push_cast; ring,
      Complex.cpow_add _ _ hNc, Complex.cpow_add _ _ hNc]
    ring
  have key := LanglandsTunnell.forall_cpow_mul_eval_eq_of_forall_lt_re N hN _ _ jd (j + e₀ - e₂) c
    (fun u hu => by rw [← keyL u, ← keyR u]; exact h u hu s) 0
  rw [← keyL 0, ← keyR 0] at key
  simpa only [neg_zero, mul_zero, Complex.cpow_zero, Polynomial.C_1, one_mul, mul_one] using key

open Polynomial in

theorem transfer (N : ℕ) (hN : 1 < N) (K : ℂ) (r : ℤ)
    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ)
    (P₀ Pd₀ Q₀ Qd₀ : Polynomial ℂ) (m₀ md₀ : ℤ)
    (hQ₀ : Q₀ ≠ 0) (hQd₀ : Qd₀ ≠ 0)
    (ha : ∀ s : ℂ, (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * Q₀.eval ((N : ℂ) ^ (-s)) =
      (N : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)))
    (hb : ∀ s : ℂ, (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * Qd₀.eval ((N : ℂ) ^ (-s)) =
      (N : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((N : ℂ) ^ (-s)) * Qd.eval ((N : ℂ) ^ (-s)))
    (hc : ∀ s : ℂ, (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((N : ℂ) ^ (-s))) * Q₀.eval ((N : ℂ) ^ s) =
      ((Polynomial.C K).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) * ((N : ℂ) ^ ((m₀ : ℂ) * (-s)) * P₀.eval ((N : ℂ) ^ s)) * Qd₀.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) * Q.eval ((N : ℂ) ^ s) =
      ((Polynomial.C K).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) * ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)

  have hsplit : ∀ a b c : ℂ, c = a + b → (N : ℂ) ^ c = (N : ℂ) ^ a * (N : ℂ) ^ b := by
    intro a b c h; rw [h, Complex.cpow_add _ _ hNc]
  have e1 : ∀ s : ℂ, (N : ℂ) ^ (((r - m₀ : ℤ) : ℂ) * s) = (N : ℂ) ^ ((r : ℂ) * s) * (N : ℂ) ^ ((m₀ : ℂ) * (-s)) :=
    fun s => hsplit _ _ _ (by push_cast; ring)
  have e2 : ∀ s : ℂ, (N : ℂ) ^ (((r - m : ℤ) : ℂ) * s) = (N : ℂ) ^ ((r : ℂ) * s) * (N : ℂ) ^ ((m : ℂ) * (-s)) :=
    fun s => hsplit _ _ _ (by push_cast; ring)
  have e0 : ∀ s : ℂ, (N : ℂ) ^ (((0 : ℤ) : ℂ) * s) = 1 := fun s => by simp

  have stepA := LanglandsTunnell.clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq N hN
    (Polynomial.C K * P₀) Q₀ (Polynomial.C K * P) Q (r - m₀) (r - m) hQ₀
    (by
      intro s
      have h := ha (-s)
      simp only [neg_neg] at h
      simp only [Polynomial.eval_mul, Polynomial.eval_C, e1, e2]

      linear_combination (K * (N : ℂ) ^ ((r : ℂ) * s)) * h.symm)
    1 Pd₀ 1 Qd₀ 0 md₀
    (by
      intro s
      have h := hc s
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, one_mul, mul_one] at h
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, one_mul, mul_one, e1, e0]
      linear_combination h)

  have stepB := LanglandsTunnell.clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq N hN
    Pd₀ Qd₀ Pd Qd (-md₀) (-md) hQd₀
    (by
      intro t
      have h := hb (-t)
      simp only [neg_neg] at h
      have f1 : (N : ℂ) ^ (((-md₀ : ℤ) : ℂ) * t) = (N : ℂ) ^ ((md₀ : ℂ) * (-t)) := by congr 1; push_cast; ring
      have f2 : (N : ℂ) ^ (((-md : ℤ) : ℂ) * t) = (N : ℂ) ^ ((md : ℂ) * (-t)) := by congr 1; push_cast; ring
      rw [f1, f2]
      linear_combination h.symm)
    1 (Polynomial.C K * P) 1 Q 0 (m - r)
    (by
      intro t
      have h := stepA (-t)
      simp only [neg_neg, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, mul_one, one_mul] at h
      have f1 : (N : ℂ) ^ (((-md₀ : ℤ) : ℂ) * t) = (N : ℂ) ^ ((md₀ : ℂ) * (-t)) := by congr 1; push_cast; ring
      have f3 : (N : ℂ) ^ (((m - r : ℤ) : ℂ) * t) = (N : ℂ) ^ (((r - m : ℤ) : ℂ) * (-t)) := by congr 1; push_cast; ring
      simp only [e0, mul_one, one_mul] at h
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, mul_one, one_mul, f1, f3, e0]
      linear_combination h.symm)

  intro s
  have h := stepB (-s)
  simp only [neg_neg, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, mul_one, one_mul] at h
  have f2 : (N : ℂ) ^ (((m - r : ℤ) : ℂ) * (-s)) = (N : ℂ) ^ ((r : ℂ) * s) * (N : ℂ) ^ ((m : ℂ) * (-s)) :=
    hsplit _ _ _ (by push_cast; ring)
  have f4 : (N : ℂ) ^ (((-md : ℤ) : ℂ) * (-s)) = (N : ℂ) ^ ((md : ℂ) * s) := by congr 1; push_cast; ring
  simp only [f2, f4, e0, mul_one, one_mul] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, one_mul]
  linear_combination h.symm

end M2PGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core.M2PGlue"

namespace M2PGlue2

open Filter Topology

theorem hlamU_slopes (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u 0 a : ℂˣ) : ℂ) = ((lam 0 a : ℂˣ) : ℂ) * ((‖(a : (p.adicCompletion ℚ))‖ : ℂ)) ^ u ∧
        ((lamU u 1 a : ℂˣ) : ℂ) = ((lam 1 a : ℂˣ) : ℂ) ∧
          ((lamU u 2 a : ℂˣ) : ℂ) = ((lam 2 a : ℂˣ) : ℂ) * ((‖(a : (p.adicCompletion ℚ))‖ : ℂ)) ^ (-u)) :
    ∀ (u : ℂ) (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : (p.adicCompletion ℚ))‖ : ℂ)) ^ (((![1, 0, -1] : Fin 3 → ℤ) i : ℂ) * u) := by
  intro u i a
  obtain ⟨h0, h1, h2⟩ := hlamU u a
  fin_cases i
  · show ((lamU u 0 a : ℂˣ) : ℂ) = ((lam 0 a : ℂˣ) : ℂ) * ((‖(a : (p.adicCompletion ℚ))‖ : ℂ)) ^ (((1 : ℤ) : ℂ) * u)
    rw [h0, Int.cast_one, one_mul]
  · show ((lamU u 1 a : ℂˣ) : ℂ) = ((lam 1 a : ℂˣ) : ℂ) * ((‖(a : (p.adicCompletion ℚ))‖ : ℂ)) ^ (((0 : ℤ) : ℂ) * u)
    rw [h1, Int.cast_zero, zero_mul, Complex.cpow_zero, mul_one]
  · show ((lamU u 2 a : ℂˣ) : ℂ) = ((lam 2 a : ℂˣ) : ℂ) * ((‖(a : (p.adicCompletion ℚ))‖ : ℂ)) ^ (((-1 : ℤ) : ℂ) * u)
    rw [h2, Int.cast_neg, Int.cast_one, neg_one_mul]

theorem jacquetWhittaker3_mul_of_cellSectionOf_mul (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → (p.adicCompletion ℚ)) → ℂ) (k : LocalGL3 p)
    (hk : ∀ h : LocalGL3 p, cellSectionOf p χ Φ (h * k) = cellSectionOf p χ Φ h) (g : LocalGL3 p) :
    jacquetWhittaker3 p χ Φ (g * k) = jacquetWhittaker3 p χ Φ g := by
  simp only [jacquetWhittaker3_apply]
  congr 1
  ext h
  show cellSectionOf p χ Φ (h * (g * k)) = cellSectionOf p χ Φ (h * g)
  rw [← mul_assoc, hk]

theorem isGL3PsiWhittakerFn_jacquetWhittaker3_translate (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (Φ : (Fin 3 → (p.adicCompletion ℚ)) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) (T : LocalGL3 p) :
    IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹
      (fun h => jacquetWhittaker3 p χ Φ (diagonal3 p ![1, -1, 1] * h * T)) := by
  obtain ⟨Λ₀, Λ₁, -, -, -, -, hΛ₁, -, hJ⟩ :=
    LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum p χ hχ
  obtain ⟨hm, hcoef⟩ := hJ Φ hΦ
  intro x y z g
  have e1 : ∀ k : LocalGL3 p,
      jacquetWhittaker3 p χ Φ (diagonal3 p ![1, -1, 1] * k) = coefficientFn Λ₁ ⟨cellSectionOf p χ Φ, hm⟩ k :=
    fun k => congrFun hcoef k
  show jacquetWhittaker3 p χ Φ (diagonal3 p ![1, -1, 1] * (upperUnipotent3 x y z * g) * T) =
    (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (x + y) * jacquetWhittaker3 p χ Φ (diagonal3 p ![1, -1, 1] * g * T)
  rw [show diagonal3 p ![1, -1, 1] * (upperUnipotent3 x y z * g) * T = diagonal3 p ![1, -1, 1] * (upperUnipotent3 x y z * (g * T)) by
      simp only [mul_assoc], e1, mul_assoc, e1]
  exact isGL3PsiWhittakerFn_coefficientFn hΛ₁ _ x y z (g * T)

theorem finite_translate (p : HeightOneSpectrum (𝓞 ℚ)) (E : ℤ → LocalGL3 p → ℂ)
    (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite) (a b : LocalGL3 p) :
    ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i (a * g * b) ≠ 0}.Finite := by
  intro C hC
  have hcont : Continuous fun g : LocalGL3 p => a * g * b :=
    (continuous_const.mul continuous_id).mul continuous_const
  refine (hEfin ((fun g => a * g * b) '' C) (hC.image hcont)).subset ?_
  rintro i ⟨g, hg, hne⟩
  exact ⟨a * g * b, ⟨g, hg, rfl⟩, hne⟩

theorem exists_open_translate (p : HeightOneSpectrum (𝓞 ℚ)) (E : ℤ → LocalGL3 p → ℂ)
    (U : Subgroup (LocalGL3 p)) (hU : IsOpen (U : Set (LocalGL3 p)))
    (hEU : ∀ (i : ℤ), ∀ k ∈ U, ∀ g : LocalGL3 p, E i (g * k) = E i g) (a b : LocalGL3 p) :
    ∃ U' : Subgroup (LocalGL3 p), IsOpen (U' : Set (LocalGL3 p)) ∧
      ∀ (i : ℤ), ∀ k ∈ U', ∀ g : LocalGL3 p, E i (a * (g * k) * b) = E i (a * g * b) := by
  refine ⟨U.comap (MulAut.conj b⁻¹).toMonoidHom, ?_, ?_⟩
  · have hc : Continuous fun x : LocalGL3 p => b⁻¹ * x * b⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hU.preimage hc
  · intro i k hk g
    have hk' : b⁻¹ * k * b⁻¹⁻¹ ∈ U := by simpa [Subgroup.mem_comap, MulAut.conj_apply] using hk
    rw [show a * (g * k) * b = (a * g * b) * (b⁻¹ * k * b⁻¹⁻¹) by group, hEU i _ hk']

theorem exists_open_forall_coeff_mul (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i)) (n : Fin 3 → ℤ)
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : (p.adicCompletion ℚ))‖ : ℂ)) ^ ((n i : ℂ) * u))
    (Φ : (Fin 3 → (p.adicCompletion ℚ)) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (E : ℤ → LocalGL3 p → ℂ)
    (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite)
    (hEsum : ∀ (u : ℂ) (g : LocalGL3 p),
      jacquetWhittaker3 p (lamU u) Φ g = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E i g) :
    ∃ U : Subgroup (LocalGL3 p), IsOpen (U : Set (LocalGL3 p)) ∧
      ∀ (i : ℤ), ∀ k ∈ U, ∀ g : LocalGL3 p, E i (g * k) = E i g := by
  obtain ⟨U, hUo, hU⟩ :=
    LanglandsTunnell.CubicInduction.exists_isOpen_forall_cellSectionOf_twistFamily_mul_eq p lam hlam n lamU hlamU Φ hΦ
  refine ⟨U, hUo, fun i k hk g => ?_⟩
  have h1N : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hfin : ∀ g' : LocalGL3 p, (Function.support fun i : ℤ => E i g').Finite := by
    intro g'
    refine (hEfin {g'} isCompact_singleton).subset ?_
    intro i hi
    exact ⟨g', Set.mem_singleton g', hi⟩
  have key := LanglandsTunnell.eq_of_forall_finsum_cpow_neg_mul_eq (Ideal.absNorm p.asIdeal) h1N
    (fun i => E i (g * k)) (fun i => E i g) (hfin _) (hfin _) (fun u => by
      rw [← hEsum u (g * k), ← hEsum u g]
      exact jacquetWhittaker3_mul_of_cellSectionOf_mul p (lamU u) Φ k (hU u k hk) g)
  exact congrFun key i

theorem span_unipotent_law (p : HeightOneSpectrum (𝓞 ℚ)) (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨h, rfl⟩ := hw
    intro x g
    show w₂base (unipotent x * g * h) = _ * w₂base (g * h)
    rw [mul_assoc, hw₂law]
  | zero => intro x g; simp
  | add w w' _ _ hw hw' => intro x g; simp only [Pi.add_apply, hw, hw', mul_add]
  | smul c w _ hw => intro x g; simp only [Pi.smul_apply, smul_eq_mul, hw]; ring

theorem span_smooth (p : HeightOneSpectrum (𝓞 ℚ)) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∃ U₂ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U₂ : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U₂, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨h, rfl⟩ := hw
    refine ⟨(AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N).comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · have hc : Continuous fun x : GL (Fin 2) (p.adicCompletion ℚ) => h⁻¹ * x * h⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2.preimage hc
    · intro k hk g
      have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
        simpa [Subgroup.mem_comap, MulAut.conj_apply] using hk
      show w₂base (g * k * h) = w₂base (g * h)
      rw [show g * k * h = (g * h) * (h⁻¹ * k * h⁻¹⁻¹) by group, hw₂K _ hk']
  | zero => exact ⟨⊤, isOpen_univ, fun k _ g => by simp⟩
  | add w w' _ _ hw hw' =>
    obtain ⟨U, hU, h1⟩ := hw
    obtain ⟨U', hU', h2⟩ := hw'
    refine ⟨U ⊓ U', hU.inter hU', fun k hk g => ?_⟩
    simp only [Pi.add_apply, h1 k hk.1 g, h2 k hk.2 g]
  | smul c w _ hw =>
    obtain ⟨U, hU, h1⟩ := hw
    exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, h1 k hk g]⟩

end M2PGlue2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core.M2PGlue"

namespace M2PGlue3

theorem pair_sum_eval (N : ℂ) (c : ℂ) (b : ℤ) (s u : ℂ) :
    (∑ ab ∈ ({((0 : ℤ), (0 : ℤ)), (2, b)} : Finset (ℤ × ℤ)),
        (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -c) ab *
          N ^ (-(ab.1 : ℂ) * s) * N ^ (-(ab.2 : ℂ) * u)) =
      (Polynomial.C 1 + Polynomial.C (-c * N ^ (-(b : ℂ) * u)) * Polynomial.X ^ 2).eval (N ^ (-s)) := by
  rw [Finset.sum_pair (by simp)]
  simp only [if_true, Prod.mk.injEq, if_false, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Int.cast_zero, Int.cast_ofNat, neg_zero, zero_mul, Complex.cpow_zero,
    mul_one]
  have h2 : N ^ (-(2 : ℂ) * s) = (N ^ (-s)) ^ 2 := by
    rw [← Complex.cpow_nat_mul]; ring_nf
  rw [if_neg (by omega), h2]
  ring

theorem pair_sum_eval_centre (N : ℂ) (c : ℂ) (b : ℤ) (s : ℂ) :
    (∑ ab ∈ ({((0 : ℤ), (0 : ℤ)), (2, b)} : Finset (ℤ × ℤ)),
        (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -c) ab * N ^ (-(ab.1 : ℂ) * s)) =
      (Polynomial.C 1 + Polynomial.C (-c) * Polynomial.X ^ 2).eval (N ^ (-s)) := by
  have h := pair_sum_eval N c b s 0
  simp only [mul_zero, Complex.cpow_zero, mul_one] at h
  exact h

theorem C_one_add_ne_zero (a : ℂ) : (Polynomial.C 1 + Polynomial.C a * Polynomial.X ^ 2 : Polynomial ℂ) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp at this

end M2PGlue3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core.M2PGlue"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (x y z : p.adicCompletion ℚ)
    (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ = fun h => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p)))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
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
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (E : Fin 3 → ℂ) (e : Fin 3 → ℤ)
    (hfe0 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe1 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe2 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 2 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 2 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 2 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 2 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 2 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 2 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :

    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
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
              ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C (((θ₀ (-1) : ℂˣ) : ℂ) * (E 0 * E 1 * E 2))).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(e 0 + e 1 + e 2) : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  intro μ₂ hμ₂ μN₂ hμN₂ w₂ hw₂ P Pd Q Qd m md σ₂ σ₃ hQ hQd int₁ int₂ rat₁ rat₂
  subst hW₃
  beta_reduce at int₁ int₂ rat₁ rat₂
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p

  obtain ⟨lamU, hlamU0, hlamU, hlc⟩ := M2PGlue.exists_twistFamily p lam hlam
  have hlamUn := M2PGlue2.hlamU_slopes p lam lamU hlamU
  obtain ⟨u₀, hu₀⟩ := M2PGlue.exists_forall_chamber_of_twistFamily p lam hlam lamU hlamU
  have h1N : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hNc : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsplit : ∀ a b c : ℂ, c = a + b → (Ideal.absNorm p.asIdeal : ℂ) ^ c = (Ideal.absNorm p.asIdeal : ℂ) ^ a * (Ideal.absNorm p.asIdeal : ℂ) ^ b := fun a b c h => by
    rw [h, Complex.cpow_add _ _ hNc]

  obtain ⟨E₀, hE₀fin, hE₀sum, -⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_twistFamily_eq_finsum_and_forall_le_jacquetTruncated3_eq
      p lam hlam ![1, 0, -1] lamU hlamUn Φ hΦ
  obtain ⟨U₀, hU₀, hE₀U⟩ :=
    M2PGlue2.exists_open_forall_coeff_mul p lam hlam ![1, 0, -1] lamU hlamUn Φ hΦ E₀ hE₀fin hE₀sum
  obtain ⟨U, hU, hEU⟩ := M2PGlue2.exists_open_translate p E₀ U₀ hU₀ hE₀U (diagonal3 p ![1, -1, 1]) (upperUnipotent3 x y z * antidiagonal3 p)
  have hEfin := M2PGlue2.finite_translate p E₀ hE₀fin (diagonal3 p ![1, -1, 1]) (upperUnipotent3 x y z * antidiagonal3 p)
  have hW : ∀ (u : ℂ) (g : LocalGL3 p), (fun (u : ℂ) (h : LocalGL3 p) => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) u g =
      ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * (fun (i : ℤ) (h : LocalGL3 p) => E₀ i (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) i g := fun u g => hE₀sum u _
  have hWc : ∀ g : LocalGL3 p, (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) g = ∑ᶠ i : ℤ, (fun (i : ℤ) (h : LocalGL3 p) => E₀ i (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) i g := by
    intro g
    have h0 := hE₀sum 0 (diagonal3 p ![1, -1, 1] * g * (upperUnipotent3 x y z * antidiagonal3 p))
    rw [hlamU0] at h0
    simpa only [mul_zero, Complex.cpow_zero, one_mul] using h0
  have hWlaw : ∀ u : ℂ, IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ ((fun (u : ℂ) (h : LocalGL3 p) => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) u) :=
    fun u => M2PGlue2.isGL3PsiWhittakerFn_jacquetWhittaker3_translate p (lamU u) (hlc u) Φ hΦ (upperUnipotent3 x y z * antidiagonal3 p)
  have hElaw :=
    LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_of_forall_isGL3PsiWhittakerFn_finsum_cpow_mul p
      (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (fun (i : ℤ) (h : LocalGL3 p) => E₀ i (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) hEfin (fun (u : ℂ) (h : LocalGL3 p) => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) hW hWlaw

  have hwlaw := M2PGlue2.span_unipotent_law p w₂base hw₂law w₂ hw₂
  have hwsm := M2PGlue2.span_smooth p N hN w₂base hw₂K w₂ hw₂

  obtain ⟨c, cd, u₁, hbridge⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval
      p lam hlam Φ hΦ x y z lamU hlamU0 hlamU θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm
      hcentral w₀p hw₀p wJ hwJ E e hfe0 hfe1 hfe2 μ₂ μN₂ w₂ hw₂

  obtain ⟨P₀, Pd₀, m₀, md₀, σ₂z, σ₃z, -, -, rat₁0, rat₂0, fe₀⟩ :=
    LanglandsTunnell.RankinSelberg.exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn
      p (fun (i : ℤ) (h : LocalGL3 p) => E₀ i (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) U hU hElaw hEU hEfin (fun (u : ℂ) (h : LocalGL3 p) => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) hW hWc w₂ hwlaw hwsm w₀p hw₀p
      (fun s : ℂ => (Polynomial.C (((θ₀ (-1) : ℂˣ) : ℂ) * (E 0 * E 1 * E 2))).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(e 0 + e 1 + e 2) : ℤ) : ℂ) * s)) (e 0 - e 2)
      ({((0 : ℤ), (0 : ℤ)), (2, -1)} : Finset (ℤ × ℤ)) ({((0 : ℤ), (0 : ℤ)), (2, 1)} : Finset (ℤ × ℤ)) (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -c) (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -cd) μ₂ μN₂
      (by
        refine ⟨max u₀ u₁, fun u hu => ?_⟩
        obtain ⟨P', Pd', m', md', σ₂', σ₃', i1, i2, r1, r2⟩ := hbridge u ((le_max_right _ _).trans_lt hu)
        obtain ⟨σ, hσ, h01, h12⟩ := hu₀ (u : ℂ) (by rw [Complex.ofReal_re]; exact (le_max_left _ _).trans_lt hu)
        have hfe0u := fun w hw => M2PGlue.hfe_shift p w θ₀ wJ (lam 0) (lamU u 0) (u : ℂ) (fun y => (hlamU u y).1)
          (E 0) (e 0) (hfe0 w hw)
        have hfe1u := fun w hw => M2PGlue.hfe_shift p w θ₀ wJ (lam 1) (lamU u 1) 0
          (fun y => by rw [Complex.cpow_zero, mul_one]; exact (hlamU u y).2.1) (E 1) (e 1) (hfe1 w hw)
        have hfe2u := fun w hw => M2PGlue.hfe_shift p w θ₀ wJ (lam 2) (lamU u 2) (-(u : ℂ)) (fun y => (hlamU u y).2.2)
          (E 2) (e 2) (hfe2 w hw)

        have hQ1 := M2PGlue3.pair_sum_eval (Ideal.absNorm p.asIdeal : ℂ) c (-1)
        have hQ2 := M2PGlue3.pair_sum_eval (Ideal.absNorm p.asIdeal : ℂ) cd 1
        have r1' : ∀ s : ℂ, σ₂' < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * iotaGL g * (upperUnipotent3 x y z * antidiagonal3 p))) w₂ * (Polynomial.C 1 + Polynomial.C (-c * (Ideal.absNorm p.asIdeal : ℂ) ^ (-((-1 : ℤ) : ℂ) * (u : ℂ))) * Polynomial.X ^ 2).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
          intro s hs; rw [← hQ1 s (u : ℂ)]; exact r1 s hs
        have r2' : ∀ s : ℂ, σ₃' < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => dualWhittakerFn3 (fun h => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * (Polynomial.C 1 + Polynomial.C (-cd * (Ideal.absNorm p.asIdeal : ℂ) ^ (-((1 : ℤ) : ℂ) * (u : ℂ))) * Polynomial.X ^ 2).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md' : ℂ) * s) * Pd'.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
          intro s hs; rw [← hQ2 s (u : ℂ)]; exact r2 s hs
        have key :=
          LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber
            p (lamU u) (hlc u) σ hσ h01 h12 Φ hΦ x y z
            (fun h => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) rfl
            θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral w₀p hw₀p wJ hwJ
            ![E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * (u : ℂ)), E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * 0),
              E 2 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 2 : ℂ) * (-(u : ℂ)))] e
            hfe0u hfe1u hfe2u μ₂ μN₂ w₂ hw₂ P' Pd' (Polynomial.C 1 + Polynomial.C (-c * (Ideal.absNorm p.asIdeal : ℂ) ^ (-((-1 : ℤ) : ℂ) * (u : ℂ))) * Polynomial.X ^ 2) (Polynomial.C 1 + Polynomial.C (-cd * (Ideal.absNorm p.asIdeal : ℂ) ^ (-((1 : ℤ) : ℂ) * (u : ℂ))) * Polynomial.X ^ 2) m' md' σ₂' σ₃'
            (M2PGlue3.C_one_add_ne_zero _) (M2PGlue3.C_one_add_ne_zero _) i1 i2 r1' r2'
        refine ⟨P', Pd', m', md', σ₂', σ₃', i1, i2, r1, r2, fun s => ?_⟩
        have hk := key s
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
          Polynomial.eval_one, one_mul] at hk
        rw [Polynomial.eval_C] at hk
        rw [hQ1 (-s) (u : ℂ), hQ2 s (u : ℂ), neg_neg, hk]
        simp only [Polynomial.eval_C, mul_zero, Complex.cpow_zero, mul_one]
        rw [hsplit ((e 0 : ℂ) * (u : ℂ)) ((e 2 : ℂ) * (-(u : ℂ))) ((((e 0 - e 2 : ℤ)) : ℂ) * (u : ℂ)) (by push_cast; ring)]
        ring)
      ⟨σ₂, int₁⟩ ⟨σ₃, int₂⟩

  have hC1 := M2PGlue3.pair_sum_eval_centre (Ideal.absNorm p.asIdeal : ℂ) c (-1)
  have hC2 := M2PGlue3.pair_sum_eval_centre (Ideal.absNorm p.asIdeal : ℂ) cd 1
  have ha := M2PGlue.s_continuation (Ideal.absNorm p.asIdeal) h1N P (Polynomial.C 1 + Polynomial.C (-c) * Polynomial.X ^ 2 : Polynomial ℂ) P₀ Q m m₀ (max σ₂ σ₂z)
    (fun s hs => by
      rw [← rat₁ s ((le_max_left _ _).trans_lt hs), ← hC1 s, ← rat₁0 s ((le_max_right _ _).trans_lt hs)]
      ring)
  have hb := M2PGlue.s_continuation (Ideal.absNorm p.asIdeal) h1N Pd (Polynomial.C 1 + Polynomial.C (-cd) * Polynomial.X ^ 2 : Polynomial ℂ) Pd₀ Qd md md₀ (max σ₃ σ₃z)
    (fun s hs => by
      rw [← rat₂ s ((le_max_left _ _).trans_lt hs), ← hC2 s, ← rat₂0 s ((le_max_right _ _).trans_lt hs)]
      ring)
  exact M2PGlue.transfer (Ideal.absNorm p.asIdeal) h1N (((θ₀ (-1) : ℂˣ) : ℂ) * (E 0 * E 1 * E 2)) (-(e 0 + e 1 + e 2))
    P Pd Q Qd m md P₀ Pd₀ (Polynomial.C 1 + Polynomial.C (-c) * Polynomial.X ^ 2 : Polynomial ℂ) (Polynomial.C 1 + Polynomial.C (-cd) * Polynomial.X ^ 2 : Polynomial ℂ) m₀ md₀ (M2PGlue3.C_one_add_ne_zero _) (M2PGlue3.C_one_add_ne_zero _) ha hb
    (fun s => by
      have f := fe₀ s
      have hC1' := hC1 (-s)
      have hC2' := hC2 s
      beta_reduce at hC1' hC2'
      rw [neg_neg] at hC1'
      rw [hC1', hC2'] at f
      rw [Polynomial.eval_one, one_mul, f])

end S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core (solution)
