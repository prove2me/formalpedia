-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_prod_row_mul_row_mul_cpow_mul_whittaker_diagOne_mul_cpow_of_admissible_of_chamber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/82431053-995d-5858-833a-3a4805f383c5

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
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_mul_principalSeries2_antidiagonal2_mul_row_mul_cpow_of_admissible_of_chamber
import Theorems.Thm_LanglandsTunnell_RankinSelberg_lintegral_prod_enorm_row_mul_row_mul_cpow_mul_whittaker_diagOne_eq_lintegral_shear_and_integrable_of_lt_top
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_prod_row_mul_row_mul_cpow_mul_whittaker_diagOne_mul_cpow_of_admissible_of_chamber
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace GJPC2

open Filter Topology NumberField.StandardAddChar
open scoped ENNReal

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem isLocallyConstant_of_open_stabiliser {f : G2 → ℂ} (U : Subgroup G2) (hU : IsOpen (U : Set G2))
    (hinv : ∀ k ∈ U, ∀ g : G2, f (g * k) = f g) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hopen : IsOpen ((fun u : G2 => g * u) '' (U : Set G2)) := (isOpenMap_mul_left g) _ hU
  have hmem : g ∈ (fun u : G2 => g * u) '' (U : Set G2) := ⟨1, U.one_mem, mul_one g⟩
  filter_upwards [hopen.mem_nhds hmem] with x hx
  obtain ⟨u, hu, rfl⟩ := hx
  exact hinv u hu g

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem row_one_antidiagonal2_mul (h : G2) :
    ((antidiagonal2 p * h : G2) : Matrix (Fin 2) (Fin 2) F) 1 = (h : Matrix (Fin 2) (Fin 2) F) 0 := by
  funext j
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, antidiagonal2_coe]

theorem norm_det_antidiagonal2_mul (h : G2) :
    ‖((Matrix.GeneralLinearGroup.det (antidiagonal2 p * h) : Fˣ) : F)‖ =
      ‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖ := by
  have hdet : Matrix.GeneralLinearGroup.det (antidiagonal2 p) = -1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, antidiagonal2_coe, Matrix.det_fin_two_of]
    simp
  rw [map_mul, hdet, Units.val_mul, Units.val_neg, Units.val_one, norm_mul, norm_neg, norm_one, one_mul]

theorem enorm_integral_ofReal_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (G : α → ℝ)
    (hG : ∀ x, 0 ≤ G x) (hGi : Integrable (fun x => ((G x : ℝ) : ℂ)) μ) :
    ‖∫ x, ((G x : ℝ) : ℂ) ∂μ‖ₑ = ∫⁻ x, ENNReal.ofReal (G x) ∂μ := by
  have hGr : Integrable G μ := by
    have := hGi.re
    simpa using this
  have h1 : ∫ x, ((G x : ℝ) : ℂ) ∂μ = ((∫ x, G x ∂μ : ℝ) : ℂ) := integral_ofReal
  rw [h1, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg hG)]
  exact ofReal_integral_eq_lintegral_ofReal hGr (Filter.Eventually.of_forall hG)

def Phi2abs (Φ₂ : (Fin 2 → F) → ℂ) : F × F → ℂ :=
  (fun c : ℂ => ((‖c‖ : ℝ) : ℂ)) ∘ Φ₂ ∘ (Homeomorph.finTwoArrow : (Fin 2 → F) ≃ₜ F × F).symm

theorem phi2abs_reg (Φ₂ : (Fin 2 → F) → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂) :
    IsLocallyConstant (Phi2abs p Φ₂) ∧ HasCompactSupport (Phi2abs p Φ₂) := by
  refine ⟨?_, ?_⟩
  · exact (hΦ₂.1.comp_continuous
      (Homeomorph.finTwoArrow : (Fin 2 → F) ≃ₜ F × F).symm.continuous).comp (fun c : ℂ => ((‖c‖ : ℝ) : ℂ))
  · exact (hΦ₂.2.comp_homeomorph (Homeomorph.finTwoArrow : (Fin 2 → F) ≃ₜ F × F).symm).comp_left
      (g := fun c : ℂ => ((‖c‖ : ℝ) : ℂ)) (by simp)

theorem phi2abs_apply_row (Φ₂ : (Fin 2 → F) → ℂ) (h : G2) :
    Phi2abs p Φ₂ ((h : Matrix (Fin 2) (Fin 2) F) 1 0, (h : Matrix (Fin 2) (Fin 2) F) 1 1) =
      ((‖Φ₂ ((h : Matrix (Fin 2) (Fin 2) F) 1)‖ : ℝ) : ℂ) := by
  have hr : (Homeomorph.finTwoArrow : (Fin 2 → F) ≃ₜ F × F).symm
      ((h : Matrix (Fin 2) (Fin 2) F) 1 0, (h : Matrix (Fin 2) (Fin 2) F) 1 1) = (h : Matrix (Fin 2) (Fin 2) F) 1 := by
    funext j
    fin_cases j <;> rfl
  simp only [Phi2abs, Function.comp_apply, hr]

theorem main

    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g)

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)

    (Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ₁ : IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁)
    (Φ₂ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ σP : ℝ, ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (s : ℂ), σP < s.re →
      Integrable (fun q : GL (Fin 2) (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ =>
          Φ₁ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) *
              ((μ 0 (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
            (w (diagOne q.2 * q.1) * ((μ 1 q.2 : ℂˣ) : ℂ) * ((modulus (q.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)))
        (μ₂.prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by
  letI iF : MeasurableSpace F := localBorel ℚ p
  letI iGL : MeasurableSpace G2 := localGLBorel ℚ p
  haveI iBGL : BorelSpace G2 := borelSpace_localGLBorel ℚ p
  obtain ⟨Uw, hUw, hUwinv⟩ := hwsm
  have hwlc : IsLocallyConstant w := isLocallyConstant_of_open_stabiliser p Uw hUw hUwinv

  obtain ⟨μa, f, hμalc, hμaval, hμanorm, hfPS, -, hfG⟩ :=
    LanglandsTunnell.RankinSelberg.exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt p σ h01 Φ₁ hΦ₁

  obtain ⟨σP, hP⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_integrable_whittaker_mul_principalSeries2_antidiagonal2_mul_row_mul_cpow_of_admissible_of_chamber
      p θ w hwlaw ⟨Uw, hUw, hUwinv⟩ hwadm hcentral μa hμalc σ hμanorm h01 f hfPS (Phi2abs p Φ₂)
      (phi2abs_reg p Φ₂ hΦ₂)
  refine ⟨σP, fun μ₂ _ s hs => ?_⟩
  have hI := hP μ₂ s hs
  have hfin := hI.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfin

  obtain ⟨-, hInt⟩ :=
    LanglandsTunnell.RankinSelberg.lintegral_prod_enorm_row_mul_row_mul_cpow_mul_whittaker_diagOne_eq_lintegral_shear_and_integrable_of_lt_top
      p w hwlc μ hμ Φ₁ hΦ₁.1 Φ₂ hΦ₂.1 s μ₂
  refine hInt ((lintegral_congr fun h => ?_).trans_lt hfin)

  beta_reduce
  obtain ⟨hint, hfeq⟩ := hfG (antidiagonal2 p * h)
  set d : ℝ := ‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖ with hd
  have hdpos : 0 < d := norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det h).ne_zero

  set G : Fˣ → ℝ := fun t => ‖Φ₁ (fun j : Fin 2 => (t : F) * (h : Matrix (Fin 2) (Fin 2) F) 0 j)‖ *
      (‖(t : F)‖ ^ (σ 0) * (‖(t : F)‖ ^ (σ 1))⁻¹ * ‖(t : F)‖) with hG
  have hGnn : ∀ t, 0 ≤ G t := fun t => by positivity
  have hrow := row_one_antidiagonal2_mul p h
  have hinteg : (fun t : Fˣ => (fun v : Fin 2 → F => ((‖Φ₁ v‖ : ℝ) : ℂ))
      (fun j : Fin 2 => (t : F) * ((antidiagonal2 p * h : G2) : Matrix (Fin 2) (Fin 2) F) 1 j) *
        ((μa 0 t : ℂˣ) : ℂ) * (((μa 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : F) : ℝ) : ℂ)) =
      fun t => ((G t : ℝ) : ℂ) := by
    funext t
    simp only [hG, hrow, hμaval, coe_modulus_eq_norm]
    push_cast
    ring
  have hint' : Integrable (fun t : Fˣ => ((G t : ℝ) : ℂ)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
    rw [← hinteg]; exact hint
  have hinner := enorm_integral_ofReal_eq (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) G hGnn hint'
  have hfval : f (antidiagonal2 p * h) =
      (((d ^ (σ 0) : ℝ)) : ℂ) * ((d : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        ∫ t, ((G t : ℝ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
    rw [hfeq, hinteg, hμaval, coe_modulus_eq_norm, norm_det_antidiagonal2_mul]

  have e1 : ‖(((d ^ (σ 0) : ℝ)) : ℂ)‖ₑ = ENNReal.ofReal (d ^ (σ 0)) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hhalf : (1 / 2 : ℂ).re = 1 / 2 := by simp
  have e2 : ‖((d : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (d ^ (1 / 2 : ℝ)) := by
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hdpos, hhalf]
  have e3 : ‖(((‖Φ₂ ((h : Matrix (Fin 2) (Fin 2) F) 1)‖ : ℝ)) : ℂ)‖ₑ = ‖Φ₂ ((h : Matrix (Fin 2) (Fin 2) F) 1)‖ₑ := by
    rw [← ofReal_norm, Complex.norm_real, norm_norm, ofReal_norm]
  have e4 : ‖((d : ℝ) : ℂ) ^ s‖ₑ = ENNReal.ofReal (d ^ s.re) := by
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hdpos]
  have i1 : ‖((μ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)‖ₑ = ENNReal.ofReal (d ^ (σ 0)) := by
    rw [← ofReal_norm, hσ 0]
  have i2 : ∀ t : Fˣ,
      ‖Φ₁ (fun j : Fin 2 => (t : F) * (h : Matrix (Fin 2) (Fin 2) F) 0 j)‖ₑ *
          ‖((μ 0 t : ℂˣ) : ℂ)‖ₑ * ‖(((μ 1 t : ℂˣ) : ℂ))⁻¹‖ₑ * ENNReal.ofReal ((modulus (t : F) : ℝ)) =
        ENNReal.ofReal (G t) := by
    intro t
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, norm_inv, hσ 0, hσ 1,
      coe_modulus_eq_norm, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    simp only [hG]
    congr 1
    ring

  rw [lintegral_congr i2, i1, coe_modulus_eq_norm]
  rw [← hd]
  rw [enorm_mul, enorm_mul, enorm_mul, hfval, enorm_mul, enorm_mul, hinner, phi2abs_apply_row, e1, e2, e3, e4]
  rw [show d ^ (s.re + 1 / 2) = d ^ s.re * d ^ (1 / 2 : ℝ) from Real.rpow_add hdpos _ _,
    ENNReal.ofReal_mul (by positivity)]
  ring

end GJPC2

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g)

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)

    (Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ₁ : IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁)
    (Φ₂ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ σP : ℝ, ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (s : ℂ), σP < s.re →
      Integrable (fun q : GL (Fin 2) (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ =>
          Φ₁ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) *
              ((μ 0 (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
            (w (diagOne q.2 * q.1) * ((μ 1 q.2 : ℂˣ) : ℂ) * ((modulus (q.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)))
        (μ₂.prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by
  exact GJPC2.main p θ w hwlaw hwsm hwadm hcentral μ hμ σ hσ h01 Φ₁ hΦ₁ Φ₂ hΦ₂

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_prod_row_mul_row_mul_cpow_mul_whittaker_diagOne_mul_cpow_of_admissible_of_chamber
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_prod_row_mul_row_mul_cpow_mul_whittaker_diagOne_mul_cpow_of_admissible_of_chamber (solution)
