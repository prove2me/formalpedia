-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_of_forall_torusZeta_fe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/52e419ff-99fa-5e96-9e95-d376a628a05c

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

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_shift
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_shift
import Theorems.Thm_LanglandsTunnell_RankinSelberg_godementZeta2_comp_transposeInvN_eq_godementZeta2_conj_of_central
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_matFourier22
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_of_forall_torusZeta_fe
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace GJWRed

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "G2" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M22" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))

theorem continuous_scalar : Continuous (fun z : Fˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)) := by
  have hval : ∀ z : Fˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : M22) = Matrix.diagonal (fun _ => (z : F)) :=
    fun z => rfl
  have hinv : ∀ z : Fˣ, (((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)⁻¹ : G2) : M22) = Matrix.diagonal (fun _ => ((z⁻¹ : Fˣ) : F)) :=
    fun z => by rw [← map_inv]; rfl
  rw [Units.continuous_iff]
  have e1 : (fun z : Fˣ => ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : M22)) =
      fun z : Fˣ => Matrix.diagonal (fun _ : Fin 2 => (z : F)) := funext hval
  have e2 : (fun z : Fˣ => (((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)⁻¹ : G2) : M22)) =
      fun z : Fˣ => Matrix.diagonal (fun _ : Fin 2 => ((z⁻¹ : Fˣ) : F)) := funext hinv
  refine ⟨?_, ?_⟩
  · show Continuous fun z : Fˣ => ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : M22)
    rw [e1]
    refine continuous_matrix fun i j => ?_
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq]; exact Units.continuous_val
    · simp only [Matrix.diagonal_apply_ne _ h]; exact continuous_const
  · show Continuous fun z : Fˣ => (((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)⁻¹ : G2) : M22)
    rw [e2]
    refine continuous_matrix fun i j => ?_
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq]; exact Units.continuous_val.comp continuous_inv
    · simp only [Matrix.diagonal_apply_ne _ h]; exact continuous_const

theorem isLocallyConstant_central (θ₀ : Fˣ →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (w₂base : G2 → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : G2, w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hcentral : ∀ (z : Fˣ) (g : G2), w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g) :
    IsLocallyConstant θ₀ := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, w₂base g₀ ≠ 0 := by
    by_contra h; push Not at h; exact hw₂ne (funext h)

  have htriv : ∀ z : Fˣ, (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N → θ₀ z = 1 := by
    intro z hz
    have h1 := hcentral z g₀
    have hcomm : (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) * g₀ = g₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
      apply Units.ext
      show Matrix.diagonal (fun _ => (z : F)) * (g₀ : M22) = (g₀ : M22) * Matrix.diagonal (fun _ => (z : F))
      rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [hcomm, hw₂K _ hz] at h1
    have : ((θ₀ z : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hg₀ (h1.symm.trans (one_mul _).symm)
      exact this
    exact Units.val_eq_one.1 this
  have hopen : IsOpen {z : Fˣ | (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N} :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2.preimage (continuous_scalar p)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z₀
  have hmem : z₀ ∈ (fun z => z₀⁻¹ * z) ⁻¹' {z : Fˣ | (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N} := by
    simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel, map_one]; exact one_mem _
  filter_upwards [(hopen.preimage (continuous_const.mul continuous_id)).mem_nhds hmem] with z hz
  have h1 : θ₀ (z₀⁻¹ * z) = 1 := htriv (z₀⁻¹ * z) hz
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

theorem measurePreserving_conj
    (wJ : G2) (hwJ : (wJ : M22) = !![0, 1; -1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure G2) [μ₂.IsHaarMeasure], MeasurePreserving (fun g : G2 => wJ * g * wJ⁻¹) μ₂ μ₂ := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  haveI := locallyCompactSpace_localGL ℚ p
  haveI : SecondCountableTopology M22 := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  haveI : SecondCountableTopology M22ᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M22)).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology G2 := Units.isEmbedding_embedProduct.secondCountableTopology
  intro μ₂ _
  have h4 : wJ⁻¹ ^ 4 = 1 := by
    rw [inv_pow, inv_eq_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hwJ, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have hmod : Measure.modularCharacterFun (wJ⁻¹) = 1 := by
    have : (Measure.modularCharacter (G := G2)) wJ⁻¹ ^ 4 = 1 := by rw [← map_pow, h4, map_one]
    exact (pow_eq_one_iff_of_nonneg (by simp) (by norm_num)).1 this
  have hR : MeasurePreserving (fun g : G2 => g * wJ⁻¹) μ₂ μ₂ :=
    ⟨measurable_mul_const _, by rw [Measure.map_right_mul_eq_modularCharacterFun_smul, hmod, one_smul]⟩
  have hL : MeasurePreserving (fun g : G2 => wJ * g) μ₂ μ₂ := measurePreserving_mul_left μ₂ wJ
  have : (fun g : G2 => wJ * g * wJ⁻¹) = (fun g : G2 => g * wJ⁻¹) ∘ (fun g : G2 => wJ * g) := by
    funext g; rfl
  rw [this]
  exact hR.comp hL

theorem transposeInvN_conj (wJ : G2) (hwJ : (wJ : M22) = !![0, 1; -1, 0]) (h : G2) :
    transposeInvN (Fin 2) (wJ⁻¹ * h * wJ) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det h)⁻¹ * h := by
  have hwJdet : ((wJ : M22)).det = 1 := by rw [hwJ, Matrix.det_fin_two_of]; ring
  have hwJinv : ((wJ⁻¹ : G2) : M22) = !![0, -1; 1, 0] := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, hwJdet, Ring.inverse_one, one_smul, hwJ]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hsc : ∀ u : Fˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G2) : M22) = Matrix.diagonal (fun _ => (u : F)) := fun u => rfl
  apply Units.ext
  rw [coe_transposeInvN, Units.val_mul, hsc]
  have hinv : (((wJ⁻¹ * h * wJ)⁻¹ : G2) : M22) = ((wJ⁻¹ : G2) : M22) * ((h⁻¹ : G2) : M22) * (wJ : M22) := by
    rw [show (wJ⁻¹ * h * wJ)⁻¹ = wJ⁻¹ * h⁻¹ * wJ by group]; rfl
  have hhinv : ((h⁻¹ : G2) : M22) = (((Matrix.GeneralLinearGroup.det h)⁻¹ : Fˣ) : F) •
      !![(h : M22) 1 1, -(h : M22) 0 1; -(h : M22) 1 0, (h : M22) 0 0] := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply,
      Ring.inverse_unit (Matrix.GeneralLinearGroup.det h)]
  rw [hinv, hhinv, hwJ, hwJinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.diagonal]

theorem transposeInvN_eq (wJ : G2) (hwJ : (wJ : M22) = !![0, 1; -1, 0]) (g : G2) :
    transposeInvN (Fin 2) g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det g)⁻¹ * (wJ * g * wJ⁻¹) := by
  have h := transposeInvN_conj p wJ hwJ (wJ * g * wJ⁻¹)
  have hdet : Matrix.GeneralLinearGroup.det (wJ * g * wJ⁻¹) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, map_mul, map_inv, mul_assoc, mul_comm (Matrix.GeneralLinearGroup.det g), ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [show wJ⁻¹ * (wJ * g * wJ⁻¹) * wJ = g by group, hdet] at h

theorem central_of_mem_span (θ₀ : Fˣ →* ℂˣ) (w₂base : G2 → ℂ)
    (hcentral : ∀ (z : Fˣ) (g : G2), w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w : G2 → ℂ) (hw : w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h))) :
    ∀ (z : Fˣ) (g : G2), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro z g
    show w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g * h) = ((θ₀ z : ℂˣ) : ℂ) * w₂base (g * h)
    rw [mul_assoc, hcentral]
  | zero => intro z g; simp
  | add x y _ _ hx hy => intro z g; simp only [Pi.add_apply, hx, hy, mul_add]
  | smul c x _ hx => intro z g; simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

end GJWRed

open GJWRed in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

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
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (E₀ : ℂ) (e₀ : ℤ)
    (hfe : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
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
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
          ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧

            (∀ s : ℂ, σ₂ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + 1 / 2) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w (transposeInvN (Fin 2) g) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) ∧

            (∀ s : ℂ, σ₃ < s.re →
              godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                  (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  classical
  letI := localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ _ w hw Φ hΦlc hΦcs

  have hψ0 : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    intro x hx
    apply LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← WithZero.exp_zero]; exact hx
  have hψ1 : ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
    have h := (LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
      (NumberField.StandardAddChar.psiLocal ℚ p) ⟨0, hψ0⟩ (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)).2
    rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat] at h

  set Φh : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ := matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ with hΦh
  have hΦhSB : IsSchwartzBruhat Φh :=
    LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22 p _ 0 hψ0 hψ1 Φ ⟨hΦlc, hΦcs⟩
  set cj : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) :=
    fun X => ((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X * (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) with hcj
  have hcjc : Continuous cj := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  set Φ' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ := fun X => Φh (cj X) with hΦ'
  have hΦ'lc : IsLocallyConstant Φ' := hΦhSB.1.comp_continuous hcjc
  have hΦ'cs : HasCompactSupport Φ' := by
    refine HasCompactSupport.intro (hΦhSB.2.image (show Continuous (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
      (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X * ((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) from
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)) fun X hX => ?_
    show Φh (cj X) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hmem; apply hX
    refine ⟨cj X, hmem, ?_⟩
    show (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X *
      (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) * ((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hθ : IsLocallyConstant θ₀ := GJWRed.isLocallyConstant_central p θ₀ N hN w₂base hw₂K hw₂ne hcentral
  have hcw : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g :=
    GJWRed.central_of_mem_span p θ₀ w₂base hcentral w hw
  have hχ' : IsLocallyConstant (θ₀⁻¹ * χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) := by
    have : ((θ₀⁻¹ * χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) : (p.adicCompletion ℚ)ˣ → ℂˣ) = fun z => (θ₀ z)⁻¹ * (χ z)⁻¹ := by
      funext z; rfl
    rw [this]
    exact (hθ.inv).mul hχ.inv

  obtain ⟨P, Q, m, σa, hQ, hP⟩ := LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_shift p θ₀ N hN
    w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral χ hχ μ₂ w hw Φ hΦlc hΦcs (1 / 2)
  obtain ⟨σb, hI⟩ := LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_shift p θ₀ N hN
    w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral χ hχ μ₂ w hw Φ hΦlc hΦcs (1 / 2)
  obtain ⟨Pd, Qd, md, σc, hQd, hPd⟩ := LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_shift p θ₀ N hN
    w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral (θ₀⁻¹ * χ⁻¹) hχ' μ₂ w hw Φ' hΦ'lc hΦ'cs (3 / 2)
  obtain ⟨σd, hId⟩ := LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_shift p θ₀ N hN
    w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral (θ₀⁻¹ * χ⁻¹) hχ' μ₂ w hw Φ' hΦ'lc hΦ'cs (3 / 2)
  refine ⟨P, Pd, Q, Qd, m, md, max σa σb, max σc σd, hQ, hQd, ?_, ?_, ?_, ?_⟩
  · intro s hs; exact hI s (lt_of_le_of_lt (le_max_right _ _) hs)
  · intro s hs; exact hP s (lt_of_le_of_lt (le_max_left _ _) hs)
  ·
    intro s hs
    have hF := hId s (lt_of_le_of_lt (le_max_right _ _) hs)
    have hc := GJWRed.measurePreserving_conj p wJ hwJ μ₂
    have key : (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        w (transposeInvN (Fin 2) g) * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) =
        (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          w h * Φ' (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (((θ₀⁻¹ * χ⁻¹) (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) ∘
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => wJ * g * wJ⁻¹) := by
      funext g
      show _ = w (wJ * g * wJ⁻¹) * Φh (cj ((wJ * g * wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
        (((θ₀⁻¹ * χ⁻¹) (Matrix.GeneralLinearGroup.det (wJ * g * wJ⁻¹)) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det (wJ * g * wJ⁻¹) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)
      simp only [hcj, hΦh]
      have hdet : Matrix.GeneralLinearGroup.det (wJ * g * wJ⁻¹) = Matrix.GeneralLinearGroup.det g := by
        rw [map_mul, map_mul, map_inv, mul_assoc, mul_comm (Matrix.GeneralLinearGroup.det g), ← mul_assoc, mul_inv_cancel, one_mul]
      have hconj : ((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((wJ * g * wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
        rw [← Units.val_mul, ← Units.val_mul, show wJ⁻¹ * (wJ * g * wJ⁻¹) * wJ = g by group]
      rw [hdet, hconj, GJWRed.transposeInvN_eq p wJ hwJ g, hcw, map_inv]
      have hθχ : ((((θ₀⁻¹ * χ⁻¹) (Matrix.GeneralLinearGroup.det g)) : ℂˣ) : ℂ) =
          (((θ₀ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      rw [hθχ]; ring
    rw [key]
    exact (hc.integrable_comp hF.aestronglyMeasurable).mpr hF
  ·
    intro s hs
    have h0 := LanglandsTunnell.RankinSelberg.godementZeta2_comp_transposeInvN_eq_godementZeta2_conj_of_central p θ₀ w
      hcw wJ hwJ μ₂ (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2)
    rw [h0]
    exact hPd s (lt_of_le_of_lt (le_max_left _ _) hs)

end S_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_of_forall_torusZeta_fe
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_of_forall_torusZeta_fe (solution)
