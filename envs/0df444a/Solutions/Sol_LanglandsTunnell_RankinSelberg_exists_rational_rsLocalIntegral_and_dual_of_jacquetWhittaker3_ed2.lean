-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a9c1af26-7053-5098-a5e2-3975da9fe8ba

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
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_rsLocalIntegral_and_dual_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_norm_diagOne_mul_le_of_irreducible_admissible
import Theorems.Thm_AutomorphicForm_WhittakerModel_span_translates_stable_and_law_and_smooth_and_irreducible_and_central
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

set_option maxHeartbeats 1600000

namespace JWRATAsm

open LanglandsTunnell.CubicInduction
open scoped NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))

noncomputable def qR : ℝ := ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ)

theorem one_lt_qR : 1 < qR v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [qR]; exact_mod_cast this

theorem qR_pos : 0 < qR v := zero_lt_one.trans (one_lt_qR v)

theorem qR_eq_natCast : qR v = (Ideal.absNorm v.asIdeal : ℝ) := NNReal.coe_natCast _

theorem norm_eq_zpow_of_v_eq_exp (x : F) (m : ℤ) (hx : Valued.v x = WithZero.exp m) : ‖x‖ = qR v ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    NNReal.coe_zpow, qR]
  congr 1

theorem coe_modulus_eq_norm (x : F) : ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

theorem exists_unif : ∃ ϖ : v.adicCompletionIntegers ℚ,
    Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := by
  refine ⟨⟨(NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ), ?_⟩, ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  · exact NumberField.AdelicLevel.valued_uniformizerUnit ℚ v

theorem exists_level (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) :
    ∃ b : ℕ, v.asIdeal ^ b ∣ N ∧ ¬ v.asIdeal ^ (b + 1) ∣ N := by
  have hfin : FiniteMultiplicity v.asIdeal N :=
    FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr v.isPrime.ne_top) hN
  exact ⟨multiplicity v.asIdeal N, pow_multiplicity_dvd _ _,
    hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)⟩

theorem diagZ_eq_diagOne (π : F) (hπ : π ≠ 0) (m : ℤ) :
    UnramifiedWhittaker.diagZ π hπ m = NumberField.AdelicLevel.diagOne ((Units.mk0 π hπ) ^ m) := by
  apply Units.ext
  ext i j
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [UnramifiedWhittaker.diagZ, Matrix.diagonal]

theorem modulus_mk0_zpow (π : F) (hπ : π ≠ 0) (hv : Valued.v π = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    ((LanglandsTunnell.TateLocal.modulus (((Units.mk0 π hπ) ^ m : (F)ˣ) : F) : ℝ≥0) : ℝ) = (qR v) ^ (-m) := by
  rw [coe_modulus_eq_norm, Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow,
    norm_eq_zpow_of_v_eq_exp v π (-1) hv, ← zpow_mul]
  ring_nf

theorem self_mem_gl3CyclicSubspace (W : G₃ → ℂ) : W ∈ gl3CyclicSubspace W := by
  refine Submodule.subset_span ⟨1, ?_⟩
  funext x
  simp [gl3AmbientRightTranslate]

theorem det_iotaGL (g : G) :
    Matrix.GeneralLinearGroup.det (iotaGL g : G₃) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, coe_iotaGL, embedMat2, Matrix.det_fin_three,
    Matrix.det_fin_two]
  simp

theorem det_transposeInv3 (h : G₃) :
    Matrix.GeneralLinearGroup.det (transposeInv3 h) = (Matrix.GeneralLinearGroup.det h)⁻¹ := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, transposeInv3, Matrix.det_transpose,
    Matrix.coe_units_inv, Units.val_inv_eq_inv_val]
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

theorem det_longWeyl3 : ((Matrix.GeneralLinearGroup.det (longWeyl3 : G₃) : (F)ˣ) : F) = -1 := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, longWeyl3, Matrix.det_fin_three]

end JWRATAsm

namespace JWRATAsm

open LanglandsTunnell.CubicInduction
open scoped NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))

theorem cpow_ne_zero' {q : ℂ} (hq : q ≠ 0) (a : ℂ) : q ^ a ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _

theorem coe_modulus_det_pos (g : G) :
    0 < ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ≥0) : ℝ) := by
  exact_mod_cast LanglandsTunnell.TateLocal.modulus_pos (K := F) (Units.ne_zero _)

theorem coe_modulus_det_ne_zero (g : G) :
    (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (coe_modulus_det_pos v g).ne'

theorem coe_modulus_det_dual (h : G₃) :
    ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det (longWeyl3 * transposeInv3 h) : (F)ˣ) : F) : ℝ≥0) : ℝ) =
      (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F) : ℝ≥0) : ℝ))⁻¹ := by
  rw [coe_modulus_eq_norm, coe_modulus_eq_norm, map_mul, Units.val_mul, det_longWeyl3, det_transposeInv3,
    Units.val_inv_eq_inv_val, norm_mul, norm_neg, norm_one, one_mul, norm_inv]

theorem shift_rational {q : ℂ} (hq : q ≠ 0) (c : ℂ) {f g : ℂ → ℂ} {σ : ℝ} {P Q : Polynomial ℂ} {m : ℤ}
    (hQ : Q ≠ 0) (hfg : ∀ s : ℂ, g s = f (s - c))
    (hrat : ∀ s : ℂ, σ < s.re → f s * Q.eval (q ^ (-s)) = q ^ ((m : ℂ) * s) * P.eval (q ^ (-s))) :
    ∃ P' Q' : Polynomial ℂ, Q' ≠ 0 ∧
      ∀ s : ℂ, σ + c.re < s.re → g s * Q'.eval (q ^ (-s)) = q ^ ((m : ℂ) * s) * P'.eval (q ^ (-s)) := by
  have hqc : q ^ c ≠ 0 := cpow_ne_zero' hq c
  have hdeg : (Polynomial.C (q ^ c) * Polynomial.X).natDegree = 1 := Polynomial.natDegree_C_mul_X _ hqc
  refine ⟨Polynomial.C (q ^ (-(m : ℂ) * c)) * P.comp (Polynomial.C (q ^ c) * Polynomial.X),
    Q.comp (Polynomial.C (q ^ c) * Polynomial.X), ?_, ?_⟩
  · intro h
    have hl := Polynomial.leadingCoeff_comp (p := Q) (q := Polynomial.C (q ^ c) * Polynomial.X) (by rw [hdeg]; exact one_ne_zero)
    rw [h, Polynomial.leadingCoeff_zero, Polynomial.leadingCoeff_C_mul_X] at hl
    exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ) (pow_ne_zero _ hqc)) hl.symm
  · intro s hs
    have hs' : σ < (s - c).re := by rw [Complex.sub_re]; linarith
    have key := hrat (s - c) hs'
    have e1 : q ^ (-(s - c)) = q ^ c * q ^ (-s) := by
      rw [show -(s - c) = c + -s by ring, Complex.cpow_add _ _ hq]
    have e2 : q ^ ((m : ℂ) * (s - c)) = q ^ ((m : ℂ) * s) * q ^ (-(m : ℂ) * c) := by
      rw [show (m : ℂ) * (s - c) = (m : ℂ) * s + (-(m : ℂ) * c) by ring, Complex.cpow_add _ _ hq]
    rw [e1, e2] at key
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X]
    rw [hfg s, key]
    ring

end JWRATAsm

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

open JWRATAsm in
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
    :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
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
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  intro μ₂ _ μN₂ _ w₂ hw₂
  classical

  obtain ⟨ϖ, hϖ⟩ := JWRATAsm.exists_unif p
  have hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  obtain ⟨b, hNb⟩ := JWRATAsm.exists_level p N hN
  have hw₂Kb : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g := fun k hk g =>
    LanglandsTunnell.RankinSelberg.forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
      p N w₂base hw₂K b hNb k g hk

  obtain ⟨hVstab, hVlaw, hVsm, hVirr, hVcen⟩ :=
    AutomorphicForm.WhittakerModel.span_translates_stable_and_law_and_smooth_and_irreducible_and_central
      p w₂base hw₂law b hw₂Kb hw₂irr θ₀ hcentral
  have hmem₀ : w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) :=
    Submodule.subset_span ⟨1, by funext g; simp⟩

  obtain ⟨C, M, cc, hC, hcc, hmaj⟩ :=
    AutomorphicForm.WhittakerModel.exists_norm_diagOne_mul_le_of_irreducible_admissible
      p _ hVstab hVlaw hVsm hw₂adm hVirr θ₀ hVcen w₂base hmem₀
  have hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m) := by
    refine ⟨C, M, fun m hm k hk => ?_⟩
    rw [JWRATAsm.diagZ_eq_diagOne]
    refine ((hmaj _ k hk).1).trans ?_
    gcongr

    have hmod : ((LanglandsTunnell.TateLocal.modulus
        (((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ m :
          (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : NNReal) : ℝ) = (JWRATAsm.qR p) ^ (-m) :=
      JWRATAsm.modulus_mk0_zpow p _ hπ hϖ m
    have hq1 : 1 < JWRATAsm.qR p := JWRATAsm.one_lt_qR p
    have hq0 : 0 < JWRATAsm.qR p := JWRATAsm.qR_pos p
    have key : (((LanglandsTunnell.TateLocal.modulus
        (((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ m :
          (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) ^ M)⁻¹ : NNReal) =
        ((JWRATAsm.qR p) ^ ((M : ℝ) * (m : ℝ))).toNNReal := by
      apply NNReal.coe_injective
      rw [NNReal.coe_inv, NNReal.coe_pow, hmod, Real.coe_toNNReal _ (Real.rpow_nonneg hq0.le _),
        ← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_neg hq0.le]
      congr 1; push_cast; ring
    have hexp : (0 : ℝ) ≤ (M : ℝ) * (m : ℝ) := by positivity
    have hT : (1 : NNReal) ≤ ((JWRATAsm.qR p) ^ ((M : ℝ) * (m : ℝ))).toNNReal := by
      rw [← Real.toNNReal_one]
      apply Real.toNNReal_le_toNNReal
      calc (1 : ℝ) = (JWRATAsm.qR p) ^ (0 : ℝ) := (Real.rpow_zero _).symm
        _ ≤ (JWRATAsm.qR p) ^ ((M : ℝ) * (m : ℝ)) := Real.rpow_le_rpow_of_exponent_le hq1.le hexp
    rw [key, max_eq_right hT, Real.coe_toNNReal _ (Real.rpow_nonneg hq0.le _), ← JWRATAsm.qR_eq_natCast]

  have hw₂rec :=
    AutomorphicForm.WhittakerModel.exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
      p _ hVstab hVlaw hVsm hw₂adm hπ hϖ w₂base hmem₀

  obtain ⟨a, ω₃, W', hW'eq, hlaw', hsm', hcen', hω₃u, hadm', hgauge'⟩ :=
    LanglandsTunnell.CubicInduction.exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
      p lam hlam Φ hΦ x y z W₃ hW₃

  have hψ : (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ ≠ 1 :=
    fun h => LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p (inv_eq_one.mp h)
  have hβrat :=
    LanglandsTunnell.CubicInduction.exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn
      p _ hψ W' hlaw' hsm' hadm' ω₃ hcen' hπ hϖ b

  have h8 :=
    LanglandsTunnell.RankinSelberg.forall_exists_rational_rsLocalIntegral_and_dual_of_shellRecurrence_of_centralChar_of_rationalTorusShell_of_gauge
      p W' hlaw' hsm' hgauge' b hπ hϖ hβrat w₂base hw₂law hw₂Kb θ₀ hcentral hw₂gr hw₂rec w₀p hw₀p
      μ₂ μN₂ w₂ hw₂ W' (JWRATAsm.self_mem_gl3CyclicSubspace p W')
  obtain ⟨P, Pd, Q, Qd, m, md, σ₂, σ₃, hQ, hQd, hconv, hconvd, hrat, hratd⟩ := h8

  have hc : ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 :=
    JWRATAsm.coe_modulus_det_ne_zero p
  have hWι : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W₃ (iotaGL g) =
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(a : ℂ)) *
        W' (iotaGL g) := by
    intro g
    have h1 := hW'eq (iotaGL g)
    rw [JWRATAsm.det_iotaGL] at h1
    rw [h1, ← mul_assoc, ← Complex.cpow_add _ _ (hc g), neg_add_cancel, Complex.cpow_zero, one_mul]
  have hWdι : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), dualWhittakerFn3 W₃ (iotaGL g) =
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((a : ℂ)) *
        dualWhittakerFn3 W' (iotaGL g) := by
    intro g
    rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, hW'eq, JWRATAsm.coe_modulus_det_dual, JWRATAsm.det_iotaGL,
      Complex.ofReal_inv, Complex.inv_cpow _ _ ?_, ← Complex.cpow_neg, ← mul_assoc, ← Complex.cpow_add _ _ (hc g),
      add_neg_cancel, Complex.cpow_zero, one_mul]
    rw [Complex.arg_ofReal_of_nonneg (JWRATAsm.coe_modulus_det_pos p g).le]
    exact Real.pi_ne_zero.symm
  have hintP : ∀ s : ℂ,
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) =
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (W' (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - (a : ℂ) - 1 / 2)) := by
    intro s; funext g
    rw [hWι g, show s - (a : ℂ) - 1 / 2 = -(a : ℂ) + (s - 1 / 2) by ring, Complex.cpow_add _ _ (hc g)]
    ring
  have hintD : ∀ s : ℂ,
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) =
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (dualWhittakerFn3 W' (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - -(a : ℂ) - 1 / 2)) := by
    intro s; funext g
    rw [hWdι g, show s - -(a : ℂ) - 1 / 2 = (a : ℂ) + (s - 1 / 2) by ring, Complex.cpow_add _ _ (hc g)]
    ring

  have hΨP : ∀ s : ℂ,
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
          s (fun g => W₃ (iotaGL g)) w₂ =
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
          (s - (a : ℂ)) (fun g => W' (iotaGL g)) w₂ := by
    intro s
    simp only [RSCarrier.rsLocalIntegral]
    rw [hintP s]
  have hΨD : ∀ s : ℂ,
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
          s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) =
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
          (s - -(a : ℂ)) (fun g => dualWhittakerFn3 W' (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) := by
    intro s
    simp only [RSCarrier.rsLocalIntegral]
    rw [hintD s]

  have hq0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
    have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
    exact_mod_cast h0
  obtain ⟨P', Q', hQ', hrat'⟩ := JWRATAsm.shift_rational hq0 (a : ℂ) hQ hΨP hrat
  obtain ⟨Pd', Qd', hQd', hratd'⟩ := JWRATAsm.shift_rational hq0 (-(a : ℂ)) hQd hΨD hratd
  refine ⟨P', Pd', Q', Qd', m, md, σ₂ + a, σ₃ - a, hQ', hQd', ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hintP s]
    exact hconv (s - (a : ℂ)) (by rw [Complex.sub_re, Complex.ofReal_re]; linarith)
  · intro s hs
    rw [hintD s]
    exact hconvd (s - -(a : ℂ)) (by rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]; linarith)
  · intro s hs
    exact hrat' s (by rw [Complex.ofReal_re]; linarith)
  · intro s hs
    exact hratd' s (by rw [Complex.neg_re, Complex.ofReal_re]; linarith)

end S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2 (solution)
