-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/da1979f2-2eec-5a1b-9e78-e65661494686

import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_coefficient_of_forall_torusZeta_fe
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_sum_cpow_mul_eval_eq_cpow_mul_eval
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ), ‖((lam i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
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
          (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∃ (m : ℤ) (P : Polynomial ℂ) (σ₂ : ℝ), ∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ *
                (1 - ((θ₀ ϖ : ℂˣ) : ℂ) * ((lam 1 ϖ : ℂˣ) : ℂ) * ((lam 2 ϖ : ℂˣ) : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∃ (md : ℤ) (Pd : Polynomial ℂ) (σ₃ : ℝ), ∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) *
                (1 - (((θ₀ ϖ : ℂˣ) : ℂ) * ((lam 1 ϖ : ℂˣ) : ℂ) * ((lam 2 ϖ : ℂˣ) : ℂ))⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  intro μ₂ _ μN₂ _ w₂ hw₂

  obtain ⟨n, nj, φPS, φ₁, φ₂, wj, ℓ, c, σP, σD, hc, hφPS, hφ₁, hφ₂, hwjV, hℓ, hPrim, hDual⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2
      p lam hlam σ hσ h01 h12 Φ hΦ (upperUnipotent3 x y z * antidiagonal3 p) W₃ hW₃ θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral w₀p hw₀p
      μ₂ μN₂ w₂ hw₂

  set ϖₒ : p.adicCompletionIntegers ℚ := ⟨(ϖ : (p.adicCompletion ℚ)), by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖ, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.2 (by norm_num)⟩ with hϖₒdef
  have hπₒ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖₒ ≠ 0 := by
    simpa [hϖₒdef] using ϖ.ne_zero
  have hϖₒ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖₒ) = WithZero.exp (-1 : ℤ) := by
    simpa [hϖₒdef] using hϖ
  have hmk0 : Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖₒ) hπₒ = ϖ := by
    ext; simp [hϖₒdef]

  have hA := fun (i : Fin n) (j : Fin nj) =>
    LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
      p ϖ hϖ ![lam 1, lam 2] ?hμlc ![σ 1, σ 2] ?hσ2 ?h01' (φPS i) (hφPS i) (φ₂ i) (hφ₂ i)
      θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral w₀p hw₀p wJ hwJ ![E 1, E 2] ![e 1, e 2] ?hfe0' ?hfe1'
      μ₂ μN₂ (wj j) (hwjV j)
  have hAd := fun (i : Fin n) (j : Fin nj) =>
    LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
      p hπₒ hϖₒ ![lam 1, lam 2] ?hμlc₂ ![σ 1, σ 2] ?hσ2₂ ?h01'₂ (φPS i) (hφPS i) (φ₂ i) (hφ₂ i)
      θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral w₀p hw₀p wJ hwJ ![E 1, E 2] ![e 1, e 2] ?hfe0'₂ ?hfe1'₂
      μ₂ μN₂ (wj j) (hwjV j)
  have hZ := fun (i : Fin n) (j : Fin nj) =>
    LanglandsTunnell.RankinSelberg.forall_exists_laurent_godementZeta2_coefficient_of_forall_torusZeta_fe
      p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ (lam 0) (hlam 0) (E 0) (e 0) hfe0
      μ₂ w₂ hw₂ (ℓ j) (hℓ j) (φ₁ i) (hφ₁ i).1 (hφ₁ i).2
  choose mA PA σA hA' using hA
  choose mAd PAd σAd hAd' using hAd
  choose PZ PZd mZ mZd σZ σZd hZ' using hZ
  have hN0 : Ideal.absNorm p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
  have hNC : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hN0

  obtain ⟨m₀, P₀, hLS⟩ := LanglandsTunnell.RankinSelberg.exists_sum_cpow_mul_eval_eq_cpow_mul_eval
    (Ideal.absNorm p.asIdeal) hN0 (Fin n × Fin nj) (fun ij => mA ij.1 ij.2 + mZ ij.1 ij.2)
    (fun ij => Polynomial.C c * (PA ij.1 ij.2 * PZ ij.1 ij.2))
  obtain ⟨m₀d, P₀d, hLSd⟩ := LanglandsTunnell.RankinSelberg.exists_sum_cpow_mul_eval_eq_cpow_mul_eval
    (Ideal.absNorm p.asIdeal) hN0 (Fin n × Fin nj) (fun ij => mAd ij.1 ij.2 + mZd ij.1 ij.2)
    (fun ij => Polynomial.C (c * ((((θ₀ (-1) : ℂˣ) : ℂ) * (((lam 1 (-1) : ℂˣ) : ℂ) * ((lam 2 (-1) : ℂˣ) : ℂ))))) * (PAd ij.1 ij.2 * PZd ij.1 ij.2))

  set σbig : ℝ := |σP| + ∑ i, ∑ j, (|σA i j| + |σZ i j|) with hσbig
  set σbigd : ℝ := |σD| + ∑ i, ∑ j, (|σAd i j| + |σZd i j|) with hσbigd

  have bound : ∀ (a : ℝ) (f g : Fin n → Fin nj → ℝ) (i : Fin n) (j : Fin nj),
      a ≤ |a| + ∑ i', ∑ j', (|f i' j'| + |g i' j'|) ∧
      f i j ≤ |a| + ∑ i', ∑ j', (|f i' j'| + |g i' j'|) ∧
      g i j ≤ |a| + ∑ i', ∑ j', (|f i' j'| + |g i' j'|) := by
    intro a f g i j
    have hrow : ∀ i', 0 ≤ ∑ j', (|f i' j'| + |g i' j'|) := fun i' => Finset.sum_nonneg fun j' _ => by positivity
    have hS : 0 ≤ ∑ i', ∑ j', (|f i' j'| + |g i' j'|) := Finset.sum_nonneg fun i' _ => hrow i'
    have h1 : |f i j| + |g i j| ≤ ∑ j', (|f i j'| + |g i j'|) :=
      Finset.single_le_sum (f := fun j' => |f i j'| + |g i j'|) (fun j' _ => by positivity) (Finset.mem_univ j)
    have h2 : ∑ j', (|f i j'| + |g i j'|) ≤ ∑ i', ∑ j', (|f i' j'| + |g i' j'|) :=
      Finset.single_le_sum (f := fun i' => ∑ j', (|f i' j'| + |g i' j'|)) (fun i' _ => hrow i') (Finset.mem_univ i)
    refine ⟨?_, ?_, ?_⟩
    · linarith [le_abs_self a]
    · linarith [le_abs_self (f i j), abs_nonneg (g i j), abs_nonneg a]
    · linarith [le_abs_self (g i j), abs_nonneg (f i j), abs_nonneg a]
  have hbigP : σP ≤ σbig := by
    rcases n.eq_zero_or_pos with hn | hn
    · subst hn; simp [hσbig, le_abs_self]
    rcases nj.eq_zero_or_pos with hnj | hnj
    · subst hnj; simp [hσbig, le_abs_self]
    exact (bound σP σA σZ ⟨0, hn⟩ ⟨0, hnj⟩).1
  have hbigA : ∀ i j, σA i j ≤ σbig := fun i j => (bound σP σA σZ i j).2.1
  have hbigZ : ∀ i j, σZ i j ≤ σbig := fun i j => (bound σP σA σZ i j).2.2
  have hbigD : σD ≤ σbigd := by
    rcases n.eq_zero_or_pos with hn | hn
    · subst hn; simp [hσbigd, le_abs_self]
    rcases nj.eq_zero_or_pos with hnj | hnj
    · subst hnj; simp [hσbigd, le_abs_self]
    exact (bound σD σAd σZd ⟨0, hn⟩ ⟨0, hnj⟩).1
  have hbigAd : ∀ i j, σAd i j ≤ σbigd := fun i j => (bound σD σAd σZd i j).2.1
  have hbigZd : ∀ i j, σZd i j ≤ σbigd := fun i j => (bound σD σAd σZd i j).2.2

  have gen1 : ∀ {K T : ℂ} {A Z R : Fin n → Fin nj → ℂ},
      (∀ i j, K * (A i j * T) * Z i j = R i j) → K * (∑ i, ∑ j, A i j * Z i j) * T = ∑ i, ∑ j, R i j := by
    intro K T A Z R h
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h i j]; ring
  have gen2 : ∀ {K C T : ℂ} {A Z R : Fin n → Fin nj → ℂ},
      (∀ i j, (K * C) * (A i j * T) * Z i j = R i j) → K * (C * ∑ i, ∑ j, A i j * Z i j) * T = ∑ i, ∑ j, R i j := by
    intro K C T A Z R h
    rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h i j]; ring
  refine ⟨⟨m₀, P₀, σbig, fun s hs => ⟨(hPrim s (lt_of_le_of_lt hbigP hs)).1, ?prim⟩⟩,
          ⟨m₀d, P₀d, σbigd, fun s hs => ⟨(hDual s (lt_of_le_of_lt hbigD hs)).1, ?dual⟩⟩⟩
  case prim =>
    rw [(hPrim s (lt_of_le_of_lt hbigP hs)).2.2, ← hLS s, Fintype.sum_prod_type]
    refine gen1 fun i j => ?_
    dsimp only
    have e1 := (hA' i j s (lt_of_le_of_lt (hbigA i j) hs)).2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1
    have e2 := (hZ' i j).2.1 s (lt_of_le_of_lt (hbigZ i j) hs)
    set R2 : ℂ := (Ideal.absNorm p.asIdeal : ℂ) ^ ((mZ i j : ℂ) * s) * (PZ i j).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) with hR2
    rw [e2, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      show (((mA i j + mZ i j : ℤ)) : ℂ) * s = (mA i j : ℂ) * s + (mZ i j : ℂ) * s by push_cast; ring,
      Complex.cpow_add _ _ hNC]
    linear_combination (c * R2) * e1
  case dual =>
    rw [(hDual s (lt_of_le_of_lt hbigD hs)).2.2, ← hLSd s, Fintype.sum_prod_type]
    refine gen2 fun i j => ?_
    dsimp only
    have e1 := (hAd' i j s (lt_of_le_of_lt (hbigAd i j) hs)).2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hmk0] at e1
    have e2 := (hZ' i j).2.2.2 s (lt_of_le_of_lt (hbigZd i j) hs)
    set R2 : ℂ := (Ideal.absNorm p.asIdeal : ℂ) ^ ((mZd i j : ℂ) * s) * (PZd i j).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) with hR2
    rw [e2, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      show (((mAd i j + mZd i j : ℤ)) : ℂ) * s = (mAd i j : ℂ) * s + (mZd i j : ℂ) * s by push_cast; ring,
      Complex.cpow_add _ _ hNC]
    linear_combination (c * ((((θ₀ (-1) : ℂˣ) : ℂ) * (((lam 1 (-1) : ℂˣ) : ℂ) * ((lam 2 (-1) : ℂˣ) : ℂ)))) * R2) * e1
  case hμlc => intro i; fin_cases i <;> exact hlam _
  case hσ2 => intro i a; fin_cases i <;> exact hσ _ a
  case h01' => exact h12
  case hfe0' => intro w hw; exact hfe1 w hw
  case hfe1' => intro w hw; exact hfe2 w hw
  case hμlc₂ => intro i; fin_cases i <;> exact hlam _
  case hσ2₂ => intro i a; fin_cases i <;> exact hσ _ a
  case h01'₂ => exact h12
  case hfe0'₂ => intro w hw; exact hfe1 w hw
  case hfe1'₂ => intro w hw; exact hfe2 w hw

end

end S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber (solution)
