-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/55ddb556-efd5-55b9-bb08-e500bbb93c06

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
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace B4S
namespace QuotAbs

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem continuous_of_rightInvariant {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (F : G → ℂ) (hF : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, F (g * k) = F g) :
    Continuous F := by
  obtain ⟨U, hU, hinv⟩ := hF
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show F (g * k) ∈ s
    rw [hinv k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

theorem continuous_entry (i j : Fin 2) : Continuous (fun g : G2 => (g : Matrix (Fin 2) (Fin 2) Qp) i j) :=
  Units.continuous_val.matrix_elem i j

theorem continuous_modulus_det :
    Continuous (fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ))) := by
  have h : (fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ))) =
      fun g : G2 => ‖((g : Matrix (Fin 2) (Fin 2) Qp)).det‖ := by
    funext g
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm,
      Matrix.GeneralLinearGroup.val_det_apply]
  rw [h]
  exact (Units.continuous_val.matrix_det).norm

theorem modulus_det_pos (g : G2) : 0 < ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ)) := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm, norm_pos_iff]
  exact (Matrix.GeneralLinearGroup.det g).ne_zero

theorem continuous_modulus_det_cpow (s : ℂ) :
    Continuous fun g : G2 =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ) : ℂ) ^ s :=
  (Complex.continuous_ofReal.comp (continuous_modulus_det p)).cpow continuous_const
    (fun g => Or.inl (by simpa only [Function.comp_apply, Complex.ofReal_re] using modulus_det_pos p g))

theorem continuous_upperUnipotent2 : Continuous fun x : Qp => (upperUnipotent2 p x : G2) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : Qp => ((upperUnipotent2 p x : G2) : Matrix (Fin 2) (Fin 2) Qp)
    simp only [upperUnipotent2_coe]
    refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun x : Qp => (((upperUnipotent2 p x : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) Qp)) =
        fun x : Qp => (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) Qp) := by
      funext x; rfl
    rw [this]
    refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end B4S.QuotAbs

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

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
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ σ' : ℝ, ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure] (s : ℂ), σ' < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              w g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := by
  letI iGL : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI iBGL : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI iBF : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p

  obtain ⟨σ₀', τ, A, H⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber
      p μ hμ σ hσ h01 φ hφ θ w hwlaw hwsm hwadm hcentral φ₂ hφ₂
  refine ⟨σ₀', ?_⟩
  intro μ₂ _ μN₂ _ s hs
  obtain ⟨I, hI0, hIg⟩ := H μ₂ μN₂ s.re hs
  have hb := hIg 1
  simp only [mul_one] at hb

  obtain ⟨hSC, -, -, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hSC
  haveI : SFinite (selfDualHaarAt ℚ p) := by
    unfold selfDualHaarAt; infer_instance

  have hφc : Continuous φ := (mem_principalSeries2_iff.mp hφ).1.continuous
  have hφ₂c : Continuous φ₂ := hφ₂.1.continuous
  have hwc : Continuous w := B4S.QuotAbs.continuous_of_rightInvariant w hwsm
  have hψc : Continuous (NumberField.StandardAddChar.psiLocal ℚ p) :=
    NumberField.StandardAddChar.continuous_psiLocal ℚ p

  have hK : Continuous fun z : GL (Fin 2) (p.adicCompletion ℚ) × p.adicCompletion ℚ =>
      NumberField.StandardAddChar.psiLocal ℚ p z.2 * φ (antidiagonal2 p * upperUnipotent2 p z.2 * z.1) := by
    refine (hψc.comp continuous_snd).mul (hφc.comp ?_)
    exact (continuous_const.mul ((B4S.QuotAbs.continuous_upperUnipotent2 p).comp continuous_snd)).mul continuous_fst
  have hI : StronglyMeasurable fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
        φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p) :=
    hK.stronglyMeasurable.integral_prod_right'
  have hF : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      w g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) :=
    hwc.mul (hφ₂c.comp ((B4S.QuotAbs.continuous_entry p 1 0).prodMk (B4S.QuotAbs.continuous_entry p 1 1)))
  have hG : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2) :=
    B4S.QuotAbs.continuous_modulus_det_cpow p (s + 1 / 2 - 1 / 2)

  have hint : Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
          φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) *
        w g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := by
    refine ⟨?_, ?_⟩
    · have h3 : StronglyMeasurable fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
              φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) *
            w g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) := by
        have := hI.mul hF.stronglyMeasurable
        simp only [mul_assoc] at this ⊢
        exact this
      exact (h3.mul hG.stronglyMeasurable).aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_enorm]
      have hre : (s + 1 / 2 - 1 / 2 : ℂ).re = s.re := by rw [add_sub_cancel_right]
      have key : ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
          ‖((∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) *
              w g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)‖ₑ =
          ‖(∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) *
              w g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)‖₊ *
            ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ s.re) := by
        intro g
        rw [enorm_eq_nnnorm, nnnorm_mul, ENNReal.coe_mul]
        congr 1
        rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Complex.norm_cpow_eq_rpow_re_of_pos (B4S.QuotAbs.modulus_det_pos p g),
          hre, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm]
      calc ∫⁻ g, ‖((∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) *
              w g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)‖ₑ
            ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))
          = ∫⁻ g, ‖(∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) *
              w g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)‖₊ *
            ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ s.re)
            ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) :=
            lintegral_congr fun g => key g
        _ ≤ _ := hb
        _ < ⊤ := ENNReal.ofReal_lt_top
  exact hint.congr (Filter.Eventually.of_forall fun g => by simp only [mul_assoc])

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber (solution)
