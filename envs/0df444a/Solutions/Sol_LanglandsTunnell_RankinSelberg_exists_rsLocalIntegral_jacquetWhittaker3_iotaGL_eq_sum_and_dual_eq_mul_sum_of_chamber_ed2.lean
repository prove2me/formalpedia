-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a9944efd-1d08-54c0-a30e-44b307033a64

import Theorems.Thm_LanglandsTunnell_RankinSelberg_rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta
import Theorems.Thm_LanglandsTunnell_CubicInduction_godementWhittaker3_iotaGL_eq_of_pureTensor
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_translate_eq_mul_sum_linearMap_of_admissible
import Theorems.Thm_RSCarrier_integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_psiLocal_mul_transposeInvN_eq_mul_integral_psiLocal_mul_dual
import Theorems.Thm_LanglandsTunnell_CubicInduction_conj_transposeInvN_mem_principalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier23_leftBlock_mul_lastCol_mul_const
import Theorems.Thm_LanglandsTunnell_CubicInduction_godementDock_diagFlip_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetIntegral_principalSeries2_smooth_law_central_flip
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integrable_rsIntegrand_godementSlot_of_integrable_unfold
import Theorems.Thm_LanglandsTunnell_CubicInduction_dualSection_mem_principalSeries2_and_jacquetIntegral_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_subgroup_isOpen_isCompact_forall_apply_mul_eq_and_det_eq_one_and_transposeInv_mem
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Theorems.Thm_AutomorphicForm_WhittakerModel_forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_RankinSelberg_measure_setOf_mem_localLevelOne_top_pos_and_lt_top
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_CubicInduction_mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_matFourier22
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_colFourier23
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
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

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace C3bStandIn

theorem OMEGA_family (p : HeightOneSpectrum (𝓞 ℚ)) (ι : Type) [Fintype ι]
    (φ : ι → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : ∀ i, IsLocallyConstant (φ i) ∧ HasCompactSupport (φ i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      (∀ i, ∀ ω ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        φ i ((ω * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = φ i ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∧
      (∀ ω ∈ Ω, χ (Matrix.GeneralLinearGroup.det ω) = 1) ∧
      (∀ ω ∈ Ω, transposeInvN (Fin 2) ω ∈ Ω) := by
  classical
  have h00 : IsLocallyConstant (0 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) ∧ HasCompactSupport (0 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) :=
    ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  obtain ⟨Ω₀, h0o, h0c, -, h0χ, h0t⟩ := LanglandsTunnell.RankinSelberg.exists_subgroup_isOpen_isCompact_forall_apply_mul_eq_and_det_eq_one_and_transposeInv_mem p 0 h00 χ hχ
  choose Ω hΩ using fun i => LanglandsTunnell.RankinSelberg.exists_subgroup_isOpen_isCompact_forall_apply_mul_eq_and_det_eq_one_and_transposeInv_mem p (φ i) (hφ i) χ hχ
  refine ⟨Ω₀ ⊓ ⨅ i, Ω i, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf, Subgroup.coe_iInf]
    exact h0o.inter (isOpen_iInter_of_finite fun i => (hΩ i).1)
  · refine h0c.of_isClosed_subset ?_ (by rw [Subgroup.coe_inf]; exact Set.inter_subset_left)
    rw [Subgroup.coe_inf, Subgroup.coe_iInf]
    exact (Subgroup.isClosed_of_isOpen _ h0o).inter (isClosed_iInter fun i => Subgroup.isClosed_of_isOpen _ (hΩ i).1)
  · intro i ω hω h
    exact (hΩ i).2.2.1 ω (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hω).2 i) h
  · intro ω hω
    exact h0χ ω (Subgroup.mem_inf.1 hω).1
  · intro ω hω
    refine Subgroup.mem_inf.2 ⟨h0t ω (Subgroup.mem_inf.1 hω).1, Subgroup.mem_iInf.2 fun i => ?_⟩
    exact (hΩ i).2.2.2.2 ω (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hω).2 i)

theorem K_standin (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  obtain ⟨K, hKo, hKc, -, -, -⟩ := LanglandsTunnell.RankinSelberg.exists_subgroup_isOpen_isCompact_forall_apply_mul_eq_and_det_eq_one_and_transposeInv_mem p 0 ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩ 1 (IsLocallyConstant.const 1)
  exact ⟨K, hKo, hKc⟩

end C3bStandIn

namespace C3bGlueQ

open NumberField.StandardAddChar

section Aux

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "G₂" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))

theorem det_unipotentGL2Hom (z : Multiplicative F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2Hom z : G₂) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  show Matrix.det ((unipotentGL2 (Multiplicative.toAdd z) : G₂) : M2) = 1
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]
  ring

theorem diagonal2_inv (a : Fin 2 → Fˣ) : (diagonal2 p a)⁻¹ = diagonal2 p a⁻¹ := by
  apply Units.ext
  rfl

theorem coe_conj_diagonal2 (a : Fin 2 → Fˣ) (x : G₂) (i j : Fin 2) :
    ((diagonal2 p a * x * (diagonal2 p a)⁻¹ : G₂) : M2) i j = (a i : F) * (x : M2) i j * (((a j)⁻¹ : Fˣ) : F) := by
  have hinv : (((diagonal2 p a)⁻¹ : G₂) : M2) = Matrix.diagonal fun k => (((a k)⁻¹ : Fˣ) : F) := rfl
  rw [Units.val_mul, Units.val_mul, hinv, diagonal2_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_range_unipotentGL2Hom_iff (g : G₂) :
    g ∈ (unipotentGL2Hom (R := F)).range ↔ (g : M2) 0 0 = 1 ∧ (g : M2) 1 0 = 0 ∧ (g : M2) 1 1 = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    change ((unipotentGL2 (Multiplicative.toAdd x) : G₂) : M2) 0 0 = 1 ∧
      ((unipotentGL2 (Multiplicative.toAdd x) : G₂) : M2) 1 0 = 0 ∧
      ((unipotentGL2 (Multiplicative.toAdd x) : G₂) : M2) 1 1 = 1
    simp [unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : M2) 0 1), ?_⟩
    apply Units.ext
    change ((unipotentGL2 ((g : M2) 0 1) : G₂) : M2) = (g : M2)
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem conj_diagonal2_mem (a : Fin 2 → Fˣ) (x : G₂) (hx : x ∈ (unipotentGL2Hom (R := F)).range) :
    diagonal2 p a * x * (diagonal2 p a)⁻¹ ∈ (unipotentGL2Hom (R := F)).range := by
  rw [mem_range_unipotentGL2Hom_iff] at hx ⊢
  obtain ⟨h00, h10, h11⟩ := hx
  refine ⟨?_, ?_, ?_⟩ <;> rw [coe_conj_diagonal2]
  · rw [h00, mul_one, Units.mul_inv]
  · rw [h10, mul_zero, zero_mul]
  · rw [h11, mul_one, Units.mul_inv]

theorem continuous_det_units : Continuous fun h : G₂ => (Matrix.GeneralLinearGroup.det h : Fˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (fun h : G₂ => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F)) = fun h : G₂ => (h : M2).det :=
      funext fun h => Matrix.GeneralLinearGroup.val_det_apply h
    rw [show (Units.val ∘ fun h : G₂ => (Matrix.GeneralLinearGroup.det h : Fˣ)) =
        fun h : G₂ => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) from rfl, this]
    exact Units.continuous_val.matrix_det
  · have : (fun h : G₂ => (((Matrix.GeneralLinearGroup.det h : Fˣ)⁻¹ : Fˣ) : F)) =
        fun h : G₂ => ((h⁻¹ : G₂) : M2).det := by
      funext h
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

end Aux

theorem modulus_det_unipotent_mul (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ h ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (modulus ((Matrix.GeneralLinearGroup.det (h * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) = (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) := by
  rintro h ⟨z, rfl⟩ g
  rw [map_mul, det_unipotentGL2Hom, one_mul]

theorem mem_range_unipotentGL2Hom_iff_conj (p : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 2 → (p.adicCompletion ℚ)ˣ) :
    ∀ x : GL (Fin 2) (p.adicCompletion ℚ), x ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range ↔ diagonal2 p a * x * (diagonal2 p a)⁻¹ ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := by
  intro x
  refine ⟨conj_diagonal2_mem p a x, fun h => ?_⟩
  have h' := conj_diagonal2_mem p a⁻¹ _ h
  have e : diagonal2 p a⁻¹ * (diagonal2 p a * x * (diagonal2 p a)⁻¹) * (diagonal2 p a⁻¹)⁻¹ = x := by
    rw [← diagonal2_inv, inv_inv]
    group
  rwa [e] at h'

theorem modulus_det_diagonal2_mul (p : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 2 → (p.adicCompletion ℚ)ˣ)
    (ha : ‖((a 0 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ * ‖((a 1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ = 1) :
    ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (modulus ((Matrix.GeneralLinearGroup.det (diagonal2 p a * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) = (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) := by
  intro g
  have hdet : ((Matrix.GeneralLinearGroup.det (diagonal2 p a) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) =
      (a 0 : p.adicCompletion ℚ) * (a 1 : p.adicCompletion ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, diagonal2_coe, Matrix.det_diagonal, Fin.prod_univ_two]
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, coe_modulus_eq_norm, hdet, norm_mul, ha, one_mul]

theorem measurable_rsIntegrand (p : HeightOneSpectrum (𝓞 ℚ)) (W F' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hW : IsLocallyConstant W) (hF : IsLocallyConstant F') (s : ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    Measurable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (W g * F' g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  have hmodc : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ)) := by
    have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ))) =
        fun g => ((‖((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ : ℝ) : ℂ) :=
      funext fun g => by rw [coe_modulus_eq_norm]
    rw [this]
    exact Complex.continuous_ofReal.comp ((Units.continuous_val.comp (continuous_det_units p)).norm)
  exact (hW.continuous.measurable.mul hF.continuous.measurable).mul (hmodc.measurable.pow_const _)

section Aux2

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "G₂" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))

theorem unipotent_eq_unipotentGL2 (x : F) : (unipotent x : G₂) = unipotentGL2 x :=
  Units.ext rfl

theorem unipotentGL2_mul_apply_one (x : F) (g : G₂) (j : Fin 2) :
    ((unipotentGL2 x * g : G₂) : M2) 1 j = (g : M2) 1 j := by
  rw [Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp

end Aux2

theorem isLocallyConstant_modulus_det (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsLocallyConstant (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ)) := by
  have hdet := continuous_det_units p
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hd0 : ((Matrix.GeneralLinearGroup.det g₀ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) ≠ 0 :=
    (Matrix.GeneralLinearGroup.det g₀).ne_zero
  have e2 : ∀ᶠ g in nhds g₀,
      ‖((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ =
        ‖((Matrix.GeneralLinearGroup.det g₀ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ :=
    (Units.continuous_val.comp hdet).continuousAt.eventually (eventually_norm_eq p hd0)
  filter_upwards [e2] with g hg
  rw [coe_modulus_eq_norm, coe_modulus_eq_norm, hg]

theorem pair22_unipotent_invariant (p : HeightOneSpectrum (𝓞 ℚ))
    (W F' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (φr : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
    (hW : ∀ (t : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), W (unipotent t * g) = psiLocal ℚ p (-t) * W g)
    (hF : ∀ (t : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), F' (unipotent t * g) = psiLocal ℚ p t * F' g) :
    ∀ h ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      W (h * g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => F' g * φr (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) (h * g) =
        W g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => F' g * φr (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g := by
  rintro h ⟨z, rfl⟩ g
  have hh : (unipotentGL2Hom z : GL (Fin 2) (p.adicCompletion ℚ)) = unipotent (Multiplicative.toAdd z) := by
    rw [unipotent_eq_unipotentGL2]; rfl
  simp only []
  rw [hh, hW, hF, unipotent_eq_unipotentGL2, unipotentGL2_mul_apply_one, unipotentGL2_mul_apply_one]
  have hψ : psiLocal ℚ p (-Multiplicative.toAdd z) * psiLocal ℚ p (Multiplicative.toAdd z) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc psiLocal ℚ p (-Multiplicative.toAdd z) * W g * (psiLocal ℚ p (Multiplicative.toAdd z) * F' g * φr _)
      = (psiLocal ℚ p (-Multiplicative.toAdd z) * psiLocal ℚ p (Multiplicative.toAdd z)) * (W g * (F' g * φr _)) := by ring
    _ = W g * (F' g * φr _) := by rw [hψ, one_mul]

section Q3aux

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "G₂" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))

def conjN (a : Fin 2 → Fˣ) :
    ↥(unipotentGL2Hom (R := F)).range ≃* ↥(unipotentGL2Hom (R := F)).range where
  toFun x := ⟨diagonal2 p a * (x : G₂) * (diagonal2 p a)⁻¹,
    (mem_range_unipotentGL2Hom_iff_conj p a (x : G₂)).1 x.2⟩
  invFun x := ⟨diagonal2 p a⁻¹ * (x : G₂) * (diagonal2 p a⁻¹)⁻¹,
    (mem_range_unipotentGL2Hom_iff_conj p a⁻¹ (x : G₂)).1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    show diagonal2 p a⁻¹ * (diagonal2 p a * (x : G₂) * (diagonal2 p a)⁻¹) * (diagonal2 p a⁻¹)⁻¹ = (x : G₂)
    rw [← diagonal2_inv, inv_inv]
    group
  right_inv x := by
    apply Subtype.ext
    show diagonal2 p a * (diagonal2 p a⁻¹ * (x : G₂) * (diagonal2 p a⁻¹)⁻¹) * (diagonal2 p a)⁻¹ = (x : G₂)
    rw [← diagonal2_inv, inv_inv]
    group
  map_mul' x y := by
    apply Subtype.ext
    show diagonal2 p a * ((x : G₂) * (y : G₂)) * (diagonal2 p a)⁻¹ =
      diagonal2 p a * (x : G₂) * (diagonal2 p a)⁻¹ * (diagonal2 p a * (y : G₂) * (diagonal2 p a)⁻¹)
    group

theorem conjN_apply (a : Fin 2 → Fˣ) (x : ↥(unipotentGL2Hom (R := F)).range) :
    conjN p a x = ⟨diagonal2 p a * (x : G₂) * (diagonal2 p a)⁻¹,
      (mem_range_unipotentGL2Hom_iff_conj p a (x : G₂)).1 x.2⟩ := rfl

theorem coe_conjN (a : Fin 2 → Fˣ) (x : ↥(unipotentGL2Hom (R := F)).range) :
    ((conjN p a x : ↥(unipotentGL2Hom (R := F)).range) : G₂) = diagonal2 p a * (x : G₂) * (diagonal2 p a)⁻¹ := rfl

theorem coe_conjN_symm (a : Fin 2 → Fˣ) (x : ↥(unipotentGL2Hom (R := F)).range) :
    (((conjN p a).symm x : ↥(unipotentGL2Hom (R := F)).range) : G₂) =
      diagonal2 p a⁻¹ * (x : G₂) * (diagonal2 p a⁻¹)⁻¹ := rfl

theorem continuous_conjN (a : Fin 2 → Fˣ) : Continuous (conjN p a) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem continuous_conjN_symm (a : Fin 2 → Fˣ) : Continuous (conjN p a).symm := by
  have : ((conjN p a).symm : ↥(unipotentGL2Hom (R := F)).range → ↥(unipotentGL2Hom (R := F)).range) =
      fun x => ⟨diagonal2 p a⁻¹ * (x : G₂) * (diagonal2 p a⁻¹)⁻¹,
        (mem_range_unipotentGL2Hom_iff_conj p a⁻¹ (x : G₂)).1 x.2⟩ := rfl
  rw [this]
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem mem_K0 (k : G₂) (h : ∀ i j, Valued.v ((k : M2) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((k⁻¹ : G₂) : M2) i j) ≤ 1) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  have aux : ∀ (m : M2), (∀ i j, Valued.v (m i j) ≤ 1) → AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m hm
    refine ⟨fun i j => by rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]; exact hm i j, ?_, ?_⟩
    · rw [NumberField.AdelicLevel.idealBound_top]; exact hm 1 0
    · rw [NumberField.AdelicLevel.idealBound_top]
      refine (Valuation.map_sub _ _ _).trans (max_le (hm 1 1) ?_)
      rw [Valuation.map_one]
  exact ⟨aux _ h, aux _ h'⟩

theorem unipotentGL2_mem_K0_iff (s : F) :
    (unipotentGL2 s : G₂) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ↔ Valued.v s ≤ 1 := by
  constructor
  · intro h
    rw [AdelicDock.mem_localLevelOne_iff] at h
    have := h.1.integral 0 1
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this
    simpa [unipotentGL2_coe] using this
  · intro hs
    have hinv : (((unipotentGL2 s : G₂)⁻¹ : G₂) : M2) = !![1, -s; 0, 1] := rfl
    refine mem_K0 p _ ?_ ?_
    · intro i j
      rw [unipotentGL2_coe]
      fin_cases i <;> fin_cases j <;> simp [hs]
    · intro i j
      rw [hinv]
      fin_cases i <;> fin_cases j <;> simp [hs]

theorem eq_unipotentGL2_of_mem (x : G₂) (hx : x ∈ (unipotentGL2Hom (R := F)).range) :
    x = unipotentGL2 ((x : M2) 0 1) := by
  obtain ⟨z, rfl⟩ := hx
  apply Units.ext
  show ((unipotentGL2 (Multiplicative.toAdd z) : G₂) : M2) =
    ((unipotentGL2 (((unipotentGL2 (Multiplicative.toAdd z) : G₂) : M2) 0 1) : G₂) : M2)
  simp [unipotentGL2_coe]

theorem valued_le_one_iff_norm_le_one (x : F) : Valued.v x ≤ 1 ↔ ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).symm

end Q3aux

theorem lintegral_comp_conj_diagonal2_eq (p : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 2 → (p.adicCompletion ℚ)ˣ)
    (ha : ‖((a 0 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ = ‖((a 1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure] (φ : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range → ENNReal), Measurable φ →
      ∫⁻ x : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, φ ⟨diagonal2 p a * (x : GL (Fin 2) (p.adicCompletion ℚ)) * (diagonal2 p a)⁻¹,
          (mem_range_unipotentGL2Hom_iff_conj p a (x : GL (Fin 2) (p.adicCompletion ℚ))).1 x.2⟩ ∂μN₂ = ∫⁻ x, φ x ∂μN₂ := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μN₂ _ φ hφ

  haveI : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ p
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have hcl : IsClosed ((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
    have hset : ((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Set (GL (Fin 2) (p.adicCompletion ℚ))) =
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0) ⁻¹' {1} ∩
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0) ⁻¹' {0} ∩
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ⁻¹' {1} := by
      ext g
      simp only [SetLike.mem_coe, mem_range_unipotentGL2Hom_iff, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, and_assoc]
    rw [hset]
    have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j := fun i j =>
      (Continuous.matrix_elem Units.continuous_val i j)
    exact ((isClosed_singleton.preimage (hc 0 0)).inter (isClosed_singleton.preimage (hc 1 0))).inter
      (isClosed_singleton.preimage (hc 1 1))
  haveI : LocallyCompactSpace ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range :=
    Topology.IsInducing.subtypeVal.secondCountableTopology

  have he := continuous_conjN p a
  have hes := continuous_conjN_symm p a
  have hem : Measurable (conjN p a) := he.measurable
  haveI : (Measure.map (conjN p a) μN₂).IsHaarMeasure := MulEquiv.isHaarMeasure_map μN₂ (conjN p a) he hes
  have hc := Measure.isMulLeftInvariant_eq_smul (Measure.map (conjN p a) μN₂) μN₂

  obtain ⟨hKpos, hKtop⟩ :=
    LanglandsTunnell.RankinSelberg.measure_setOf_mem_localLevelOne_top_pos_and_lt_top p μN₂
  have hKeq : {x : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range |
        (x : GL (Fin 2) (p.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤} =
      (fun x : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range =>
        ((x : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹'
        (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    conv_lhs => rw [eq_unipotentGL2_of_mem p (x : GL (Fin 2) (p.adicCompletion ℚ)) x.2]
    exact unipotentGL2_mem_K0_iff p _
  have hKm : MeasurableSet {x : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range |
      (x : GL (Fin 2) (p.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤} := by
    rw [hKeq]
    refine (IsOpen.preimage ?_ (Valued.isOpen_valuationSubring (p.adicCompletion ℚ))).measurableSet
    exact (Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) 0 1)
  have hpre : (conjN p a) ⁻¹' {x : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range |
        (x : GL (Fin 2) (p.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤} =
      {x : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range |
        (x : GL (Fin 2) (p.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤} := by
    rw [hKeq]
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      coe_conjN, coe_conj_diagonal2]
    rw [valued_le_one_iff_norm_le_one, valued_le_one_iff_norm_le_one, norm_mul, norm_mul,
      Units.val_inv_eq_inv_val, norm_inv, ← ha, mul_comm ‖((a 0 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖,
      mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (a 0).ne_zero), mul_one]
  have hK := congrArg (fun m : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range =>
    m {x : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range |
      (x : GL (Fin 2) (p.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤}) hc
  rw [Measure.map_apply hem hKm, hpre, Measure.coe_nnreal_smul_apply] at hK
  have h1 : ((Measure.map (conjN p a) μN₂).haarScalarFactor μN₂ : ENNReal) = 1 := by
    have : (1 : ENNReal) * μN₂ {x : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range |
        (x : GL (Fin 2) (p.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤} = _ := (one_mul _).trans hK
    exact ((ENNReal.mul_left_inj hKpos.ne' hKtop.ne).1 this).symm
  have hmapeq : Measure.map (conjN p a) μN₂ = μN₂ := by
    rw [hc, ENNReal.coe_eq_one.1 h1, one_smul]
  calc ∫⁻ x : ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, φ ⟨diagonal2 p a * (x : GL (Fin 2) (p.adicCompletion ℚ)) * (diagonal2 p a)⁻¹,
          (mem_range_unipotentGL2Hom_iff_conj p a (x : GL (Fin 2) (p.adicCompletion ℚ))).1 x.2⟩ ∂μN₂
      = ∫⁻ x, φ (conjN p a x) ∂μN₂ := rfl
    _ = ∫⁻ x, φ x ∂(Measure.map (conjN p a) μN₂) := (lintegral_map hφ hem).symm
    _ = ∫⁻ x, φ x ∂μN₂ := by rw [hmapeq]

section Q79aux

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "G₂" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))

theorem continuous_det_units3 : Continuous fun h : LocalGL3 p => (Matrix.GeneralLinearGroup.det h : Fˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (fun h : LocalGL3 p => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F)) =
        fun h : LocalGL3 p => (h : Matrix (Fin 3) (Fin 3) F).det :=
      funext fun h => Matrix.GeneralLinearGroup.val_det_apply h
    rw [show (Units.val ∘ fun h : LocalGL3 p => (Matrix.GeneralLinearGroup.det h : Fˣ)) =
        fun h : LocalGL3 p => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) from rfl, this]
    exact Units.continuous_val.matrix_det
  · have : (fun h : LocalGL3 p => (((Matrix.GeneralLinearGroup.det h : Fˣ)⁻¹ : Fˣ) : F)) =
        fun h : LocalGL3 p => ((h⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F).det := by
      funext h
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem isLocallyConstant_modulus_det3 :
    IsLocallyConstant (fun g : LocalGL3 p =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ)) := by
  have hdet := continuous_det_units3 p
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hd0 : ((Matrix.GeneralLinearGroup.det g₀ : Fˣ) : F) ≠ 0 := (Matrix.GeneralLinearGroup.det g₀).ne_zero
  have e2 : ∀ᶠ g in nhds g₀,
      ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ = ‖((Matrix.GeneralLinearGroup.det g₀ : Fˣ) : F)‖ :=
    (Units.continuous_val.comp hdet).continuousAt.eventually (eventually_norm_eq p hd0)
  filter_upwards [e2] with g hg
  rw [coe_modulus_eq_norm, coe_modulus_eq_norm, hg]

theorem continuous_iotaGL : Continuous (iotaGL : G₂ → LocalGL3 p) := by
  have key : ∀ (M : G₂ → M2), Continuous M → Continuous fun k => embedMat2 (M k) := by
    intro M hM
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> first
      | exact (Continuous.matrix_elem hM _ _) | exact continuous_const
  rw [Units.continuous_iff]
  exact ⟨key _ Units.continuous_val, key _ Units.continuous_coe_inv⟩

theorem continuous_transposeInv3 : Continuous (transposeInv3 : LocalGL3 p → LocalGL3 p) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun g : LocalGL3 p => Matrix.transpose ((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F)
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : LocalGL3 p => Matrix.transpose ((g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F)
    exact Units.continuous_val.matrix_transpose

theorem det_upperUnipotent3 (x y z : F) :
    Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z : LocalGL3 p) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, upperUnipotent3_coe, Matrix.det_fin_three]
  simp

theorem modulus_det_cpow_ne_zero (g : LocalGL3 p) (a : ℝ) :
    (((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (a : ℂ)) ≠ 0 := by
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  have : ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (modulus_pos (Units.ne_zero _)).ne'
  exact this h.1

theorem isLocallyConstant_of_smooth {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (f : G → ℂ) (U : Subgroup G) (hU : IsOpen (U : Set G)) (hf : ∀ k ∈ U, ∀ g : G, f (g * k) = f g) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hc : Continuous fun g : G => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hmem : ∀ᶠ g in nhds g₀, g₀⁻¹ * g ∈ (U : Set G) :=
    hc.continuousAt.eventually_mem (hU.mem_nhds (by rw [inv_mul_cancel]; exact U.one_mem))
  filter_upwards [hmem] with g hg
  rw [show g = g₀ * (g₀⁻¹ * g) by rw [mul_inv_cancel_left], hf _ hg]

theorem jacquetWhittaker3_T0_law_and_lc
    (lam : Fin 3 → (Fˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → F) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 0 0 0 * antidiagonal3 p))) ∧
    IsLocallyConstant (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 0 0 0 * antidiagonal3 p))) := by
  obtain ⟨a, ω₃, W', hW', hlaw, ⟨Uv, hUo, hUv⟩, -⟩ :=
    LanglandsTunnell.CubicInduction.exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge
      p lam hlam Φ hΦ 0 0 0
      (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ
        (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 0 0 0 * antidiagonal3 p))) rfl

  have hW0 : (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 0 0 0 * antidiagonal3 p))) =
      fun h : LocalGL3 p => ((((modulus ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) : ℝ) : ℂ) ^ (a : ℂ)))⁻¹ * W' h := by
    funext h
    rw [hW' h, inv_mul_cancel_left₀ (modulus_det_cpow_ne_zero p h a)]
  refine ⟨?_, ?_⟩
  · intro x y z h
    beta_reduce
    have key := hlaw x y z h
    rw [hW', hW', map_mul, det_upperUnipotent3, one_mul] at key
    exact mul_left_cancel₀ (modulus_det_cpow_ne_zero p h a) (by rw [key]; ring)
  · rw [hW0]
    exact ((isLocallyConstant_modulus_det3 p).comp (fun r : ℂ => (r ^ (a : ℂ))⁻¹)).mul
      (isLocallyConstant_of_smooth W' Uv hUo hUv)

theorem jacquetWhittaker3_translate_law_and_lc
    (lam : Fin 3 → (Fˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → F) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) (T : LocalGL3 p) :
    IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * T)) ∧
    IsLocallyConstant (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * h * T)) := by
  obtain ⟨hlaw0, hlc0⟩ := jacquetWhittaker3_T0_law_and_lc p lam hlam Φ hΦ
  have heq : (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * h * T)) =
      (fun h : LocalGL3 p => jacquetWhittaker3 p lam Φ
        (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 0 0 0 * antidiagonal3 p))) ∘
        (fun h : LocalGL3 p => h * T * (upperUnipotent3 0 0 0 * antidiagonal3 p)⁻¹) := by
    funext h
    simp only [Function.comp_apply]
    congr 1
    group
  refine ⟨?_, ?_⟩
  · intro x y z h
    beta_reduce
    have key := hlaw0 x y z (h * T * (upperUnipotent3 0 0 0 * antidiagonal3 p)⁻¹)
    beta_reduce at key
    have e1 : diagonal3 p ![1, -1, 1] * (upperUnipotent3 x y z * (h * T * (upperUnipotent3 0 0 0 * antidiagonal3 p)⁻¹)) *
        (upperUnipotent3 0 0 0 * antidiagonal3 p) = diagonal3 p ![1, -1, 1] * (upperUnipotent3 x y z * h) * T := by
      group
    have e2 : diagonal3 p ![1, -1, 1] * (h * T * (upperUnipotent3 0 0 0 * antidiagonal3 p)⁻¹) *
        (upperUnipotent3 0 0 0 * antidiagonal3 p) = diagonal3 p ![1, -1, 1] * h * T := by
      group
    rw [e1, e2] at key
    exact key
  · rw [heq]
    exact hlc0.comp_continuous ((continuous_id.mul continuous_const).mul continuous_const)

end Q79aux

theorem dual_pair_unipotent_invariant (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → (p.adicCompletion ℚ)) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ = fun h => jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * h * T))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = psiLocal ℚ p x * w g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : ((w₀p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    ∀ h ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 W₃ (iotaGL g)) (h * g) *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) (h * g) =
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 W₃ (iotaGL g)) g *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) g := by
  rintro h ⟨z, rfl⟩ g
  have hlawT := (jacquetWhittaker3_translate_law_and_lc p lam hlam Φ hΦ T).1
  rw [← hW₃] at hlawT
  have hdual : IsGL3PsiWhittakerFn ((psiLocal ℚ p)⁻¹)⁻¹ (dualWhittakerFn3 W₃) :=
    LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_dualWhittakerFn3 _ W₃ hlawT
  have hw₀ : w₀p = (AutomorphicForm.gl2Weyl : GL (Fin 2) (p.adicCompletion ℚ)) :=
    Units.ext (by rw [hw₀p, AutomorphicForm.gl2Weyl_val])
  have hn : (unipotentGL2Hom z : GL (Fin 2) (p.adicCompletion ℚ)) = unipotent (Multiplicative.toAdd z) := by
    rw [unipotent_eq_unipotentGL2]; rfl
  have hdet : Matrix.GeneralLinearGroup.det (unipotentGL2Hom z * g : GL (Fin 2) (p.adicCompletion ℚ)) =
      Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, det_unipotentGL2Hom, one_mul]
  beta_reduce
  rw [hdet, hn, map_mul, hw₀]
  have key := LanglandsTunnell.CubicInduction.mul_dual_eq_of_isGL3PsiWhittakerFn_inv_of_unipotent p
    ((psiLocal ℚ p)⁻¹) rfl (dualWhittakerFn3 W₃) hdual w hw (Multiplicative.toAdd z) (iotaGL g) g
  calc dualWhittakerFn3 W₃ (iotaGL (unipotent (Multiplicative.toAdd z)) * iotaGL g) *
        ((((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ)) *
          w (AutomorphicForm.gl2Weyl * transposeInvN (Fin 2) (unipotent (Multiplicative.toAdd z) * g)))
      = (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ)) *
          (dualWhittakerFn3 W₃ (iotaGL (unipotent (Multiplicative.toAdd z)) * iotaGL g) *
            w (AutomorphicForm.gl2Weyl * transposeInvN (Fin 2) (unipotent (Multiplicative.toAdd z) * g))) := by ring
    _ = (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ)) *
          (dualWhittakerFn3 W₃ (iotaGL g) * w (AutomorphicForm.gl2Weyl * transposeInvN (Fin 2) g)) := by rw [key]
    _ = _ := by ring

theorem isLocallyConstant_jacquetWhittaker3_iotaGL_and_dual (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → (p.adicCompletion ℚ)) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ = fun h => jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * h * T)) :
    IsLocallyConstant (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₃ (iotaGL g)) ∧
    IsLocallyConstant (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 W₃ (iotaGL g)) := by
  have hW₃lc : IsLocallyConstant W₃ := by
    rw [hW₃]; exact (jacquetWhittaker3_translate_law_and_lc p lam hlam Φ hΦ T).2
  refine ⟨hW₃lc.comp_continuous (continuous_iotaGL p), ?_⟩
  have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 W₃ (iotaGL g)) =
      W₃ ∘ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => longWeyl3 * transposeInv3 (iotaGL g : LocalGL3 p)) := rfl
  rw [this]
  exact hW₃lc.comp_continuous (continuous_const.mul ((continuous_transposeInv3 p).comp (continuous_iotaGL p)))

end C3bGlueQ

namespace C3bGlueSB

open NumberField.StandardAddChar

section Aux

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "M2" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
local notation "Mx" => (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ))

theorem level_zero :
    (∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → psiLocal ℚ p x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ psiLocal ℚ p x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : F, Valued.v x ≤ WithZero.exp k → psiLocal ℚ p x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
    (psiLocal ℚ p) hk (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

theorem isCompact_box (D : Fin 2 → Fin 3 → Set F) (hD : ∀ i j, IsCompact (D i j)) :
    IsCompact {Y : Mx | ∀ i j, Y i j ∈ D i j} := by
  have : {Y : Mx | ∀ i j, Y i j ∈ D i j} =
      (Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => D i j)) : Set (Fin 2 → Fin 3 → F)) := by
    ext Y
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => hD i j

theorem isLocallyConstant_indicator_integers :
    IsLocallyConstant ((p.adicCompletionIntegers ℚ : Set F).indicator fun _ => (1 : ℂ)) := by
  have hO : IsOpen (p.adicCompletionIntegers ℚ : Set F) := Valued.isOpen_valuationSubring F
  have hC : IsClosed (p.adicCompletionIntegers ℚ : Set F) := by
    rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact.isClosed
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro c
  by_cases h1 : c = 1
  · subst h1
    by_cases h10 : (1 : ℂ) = 0
    · exact absurd h10 one_ne_zero
    · have : ((p.adicCompletionIntegers ℚ : Set F).indicator fun _ => (1 : ℂ)) ⁻¹' {1} =
          (p.adicCompletionIntegers ℚ : Set F) := by
        ext x; by_cases hx : x ∈ (p.adicCompletionIntegers ℚ : Set F) <;> simp [hx]
      rw [this]; exact hO
  · by_cases h0 : c = 0
    · subst h0
      have : ((p.adicCompletionIntegers ℚ : Set F).indicator fun _ => (1 : ℂ)) ⁻¹' {0} =
          (p.adicCompletionIntegers ℚ : Set F)ᶜ := by
        ext x; by_cases hx : x ∈ (p.adicCompletionIntegers ℚ : Set F) <;> simp [hx]
      rw [this]; exact hC.isOpen_compl
    · have : ((p.adicCompletionIntegers ℚ : Set F).indicator fun _ => (1 : ℂ)) ⁻¹' {c} = ∅ := by
        ext x
        by_cases hx : x ∈ (p.adicCompletionIntegers ℚ : Set F)
        · simp [hx, Ne.symm h1]
        · simp [hx, Ne.symm h0]
      rw [this]; exact isOpen_empty

def pad (φ : F × F → ℂ) (Y : Mx) : ℂ :=
  ((p.adicCompletionIntegers ℚ : Set F).indicator (fun _ => (1 : ℂ)) (Y 0 0) *
    (p.adicCompletionIntegers ℚ : Set F).indicator (fun _ => (1 : ℂ)) (Y 0 1)) *
  ((p.adicCompletionIntegers ℚ : Set F).indicator (fun _ => (1 : ℂ)) (Y 1 0) *
    (p.adicCompletionIntegers ℚ : Set F).indicator (fun _ => (1 : ℂ)) (Y 1 1)) *
  φ (Y 0 2, Y 1 2)

theorem isSchwartzBruhat_pad (φ : F × F → ℂ) (hφ : IsLocallyConstant φ ∧ HasCompactSupport φ) :
    IsSchwartzBruhat (pad p φ) := by
  have hind := isLocallyConstant_indicator_integers p
  have hent : ∀ i : Fin 2, ∀ j : Fin 3, Continuous fun Y : Mx => Y i j := fun i j => continuous_apply_apply i j
  have hcol : Continuous fun Y : Mx => (Y 0 2, Y 1 2) := (hent 0 2).prodMk (hent 1 2)
  refine ⟨?_, ?_⟩
  · unfold pad
    exact (((hind.comp_continuous (hent 0 0)).mul (hind.comp_continuous (hent 0 1))).mul
      ((hind.comp_continuous (hent 1 0)).mul (hind.comp_continuous (hent 1 1)))).mul
      (hφ.1.comp_continuous hcol)
  ·
    have hK := hφ.2
    set D : Fin 2 → Fin 3 → Set F := fun i j =>
      if j = 2 then (if i = 0 then Prod.fst '' tsupport φ else Prod.snd '' tsupport φ)
      else (p.adicCompletionIntegers ℚ : Set F) with hDdef
    have hO : IsCompact (p.adicCompletionIntegers ℚ : Set F) := by
      rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
      exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact
    have hD : ∀ i j, IsCompact (D i j) := by
      intro i j
      simp only [hDdef]
      split_ifs
      · exact hK.image continuous_fst
      · exact hK.image continuous_snd
      · exact hO
    refine HasCompactSupport.intro (isCompact_box p D hD) fun Y hY => ?_
    by_contra hne
    apply hY
    unfold pad at hne
    have h00 : Y 0 0 ∈ (p.adicCompletionIntegers ℚ : Set F) := by
      by_contra h; apply hne; simp [Set.indicator_of_notMem h]
    have h01 : Y 0 1 ∈ (p.adicCompletionIntegers ℚ : Set F) := by
      by_contra h; apply hne; simp [Set.indicator_of_notMem h]
    have h10 : Y 1 0 ∈ (p.adicCompletionIntegers ℚ : Set F) := by
      by_contra h; apply hne; simp [Set.indicator_of_notMem h]
    have h11 : Y 1 1 ∈ (p.adicCompletionIntegers ℚ : Set F) := by
      by_contra h; apply hne; simp [Set.indicator_of_notMem h]
    have h2 : (Y 0 2, Y 1 2) ∈ tsupport φ := by
      by_contra h; apply hne; simp [image_eq_zero_of_notMem_tsupport h]
    intro i j
    fin_cases i <;> fin_cases j
    · show Y 0 0 ∈ D 0 0
      rw [hDdef]; simpa using h00
    · show Y 0 1 ∈ D 0 1
      rw [hDdef]; simpa using h01
    · show Y 0 2 ∈ D 0 2
      rw [hDdef]; simp only [if_true]; exact ⟨_, h2, rfl⟩
    · show Y 1 0 ∈ D 1 0
      rw [hDdef]; simpa using h10
    · show Y 1 1 ∈ D 1 1
      rw [hDdef]; simpa using h11
    · show Y 1 2 ∈ D 1 2
      rw [hDdef]; simp only [if_true, one_ne_zero, if_false]; exact ⟨_, h2, rfl⟩

def colEmbed (v : F × F) : Mx := Matrix.of fun i k => if k = 2 then (if i = 0 then v.1 else v.2) else 0

theorem continuous_colEmbed : Continuous (colEmbed p) := by
  refine continuous_matrix fun i k => ?_
  simp only [colEmbed, Matrix.of_apply]
  split_ifs
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_const

theorem colFourier23_pad_colEmbed (φ : F × F → ℂ) (v : F × F) :
    letI : MeasurableSpace F := localBorel ℚ p
    colFourier23 p (psiLocal ℚ p) 2 (pad p φ) (colEmbed p v) =
      ∫ u : F × F, φ u * psiLocal ℚ p (u.1 * v.1 + u.2 * v.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  letI : MeasurableSpace F := localBorel ℚ p
  rw [colFourier23_apply]
  congr 1
  funext u
  simp [pad, setCol23_apply, colEmbed]

end Aux

theorem matFourier22_psiLocal_lc_cs (p : HeightOneSpectrum (𝓞 ℚ)) (φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hφ : IsLocallyConstant φ ∧ HasCompactSupport φ) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    IsLocallyConstant (matFourier22 p (psiLocal ℚ p) φ) ∧ HasCompactSupport (matFourier22 p (psiLocal ℚ p) φ) := by
  obtain ⟨h0, h1⟩ := level_zero p
  exact LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22 p (psiLocal ℚ p) 0 h0 h1 φ hφ

theorem colPairFourier_psiLocal_lc_cs (p : HeightOneSpectrum (𝓞 ℚ)) (φ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
    (hφ : IsLocallyConstant φ ∧ HasCompactSupport φ) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    IsLocallyConstant (fun v : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) => ∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ u * psiLocal ℚ p (u.1 * v.1 + u.2 * v.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) ∧
    HasCompactSupport (fun v : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) => ∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ u * psiLocal ℚ p (u.1 * v.1 + u.2 * v.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  obtain ⟨h0, h1⟩ := level_zero p
  have hSB := LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23 p (psiLocal ℚ p) 0 h0 h1 2 (pad p φ)
    (isSchwartzBruhat_pad p φ hφ)
  have heq : (fun v : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) => ∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ),
      φ u * psiLocal ℚ p (u.1 * v.1 + u.2 * v.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) =
      colFourier23 p (psiLocal ℚ p) 2 (pad p φ) ∘ colEmbed p := by
    funext v
    exact (colFourier23_pad_colEmbed p φ v).symm
  rw [heq]
  refine ⟨hSB.1.comp_continuous (continuous_colEmbed p), ?_⟩
  have hlast : Continuous fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => (Y 0 2, Y 1 2) :=
    (continuous_apply_apply 0 2).prodMk (continuous_apply_apply 1 2)
  refine HasCompactSupport.intro (hSB.2.image hlast) fun v hv => ?_
  simp only [Function.comp_apply]
  by_contra hne
  apply hv
  refine ⟨colEmbed p v, subset_tsupport _ hne, ?_⟩
  simp [colEmbed]

theorem leftBlock_mul_lastCol_lc_cs (p : HeightOneSpectrum (𝓞 ℚ)) (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
    (hφ₁ : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁) (hφ₂ : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂) :
    IsLocallyConstant (fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => φ₁ (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ (X 0 2, X 1 2)) ∧
    HasCompactSupport (fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => φ₁ (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ (X 0 2, X 1 2)) := by
  have hent : ∀ i : Fin 2, ∀ j : Fin 3, Continuous fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => Y i j :=
    fun i j => continuous_apply_apply i j
  have hL : Continuous fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) =>
      (Matrix.of fun a b => X a (Fin.castSucc b) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    continuous_matrix fun a b => hent a (Fin.castSucc b)
  have hC : Continuous fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => (X 0 2, X 1 2) :=
    (hent 0 2).prodMk (hent 1 2)
  refine ⟨(hφ₁.1.comp_continuous hL).mul (hφ₂.1.comp_continuous hC), ?_⟩

  set D : Fin 2 → Fin 3 → Set (p.adicCompletion ℚ) := fun i j =>
    Fin.lastCases (if i = 0 then Prod.fst '' tsupport φ₂ else Prod.snd '' tsupport φ₂)
      (fun j' : Fin 2 => (fun M : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => M i j') '' tsupport φ₁) j with hDdef
  have hD : ∀ i j, IsCompact (D i j) := by
    intro i j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp only [hDdef, Fin.lastCases_last]
      split_ifs
      · exact hφ₂.2.image continuous_fst
      · exact hφ₂.2.image continuous_snd
    · simp only [hDdef, Fin.lastCases_castSucc]
      exact hφ₁.2.image (continuous_apply_apply i j')
  refine HasCompactSupport.intro (isCompact_box p D hD) fun Y hY => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hY
  obtain ⟨i, j, hij⟩ := hY
  revert hij
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · intro hij
    simp only [hDdef, Fin.lastCases_last] at hij
    have : φ₂ (Y 0 2, Y 1 2) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      fin_cases i
      · exact hij ⟨_, h, rfl⟩
      · exact hij ⟨_, h, rfl⟩
    simp [this]
  · intro hij
    simp only [hDdef, Fin.lastCases_castSucc] at hij
    have : φ₁ (Matrix.of fun a b => Y a (Fin.castSucc b)) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hij ⟨_, h, rfl⟩
    simp [this]

end C3bGlueSB

namespace C3bGlue

theorem rsLocalIntegral_const_mul {H : Type*} [Group H] [TopologicalSpace H] [MeasurableSpace H]
    (μ : Measure H) (N : Subgroup H) (μN : Measure N) (δ : H → ℝ) (s : ℂ) (a b : ℂ) (W Fn : H → ℂ) :
    RSCarrier.rsLocalIntegral μ N μN δ s (fun g => a * W g) (fun g => b * Fn g) =
      (a * b) * RSCarrier.rsLocalIntegral μ N μN δ s W Fn := by
  simp only [RSCarrier.rsLocalIntegral]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext g
  ring

end C3bGlue

open C3bStandIn NumberField.StandardAddChar in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ), ‖((lam i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p)
    (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ = fun h => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * T))

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
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ (n nj : ℕ) (φPS : Fin n → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₁ : Fin n → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : Fin n → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
            (wj : Fin nj → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (ℓ : Fin nj → (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (σP σD : ℝ),
            c ≠ 0 ∧
            (∀ i, φPS i ∈ principalSeries2 p ![lam 1, lam 2]) ∧
            (∀ i, IsLocallyConstant (φ₁ i) ∧ HasCompactSupport (φ₁ i)) ∧
            (∀ i, IsLocallyConstant (φ₂ i) ∧ HasCompactSupport (φ₂ i)) ∧
            (∀ j, wj j ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) ∧
            (∀ j, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
              ∀ k ∈ U, ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓ j (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * k)) = ℓ j v) ∧

            (∀ s : ℂ, σP < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
              (∀ i j, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                    φPS i (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  wj j g * φ₂ i (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∧
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * g)) * φ₁ i ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((lam 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s (fun g => W₃ (iotaGL g)) w₂ =
                c * ∑ i, ∑ j,
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          (s + 1 / 2) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                    φPS i (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  wj j g * φ₂ i (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
                    godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * g))) (φ₁ i) (lam 0) (s + 1 / 2)) ∧

            (∀ s : ℂ, σD < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
              (∀ i j, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                    φPS i (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ i u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∧
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * transposeInvN (Fin 2) g)) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (φ₁ i) ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  (((lam 0)⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) ∧
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) =
                c * ((((θ₀ (-1) : ℂˣ) : ℂ) * (((lam 1 (-1) : ℂˣ) : ℂ) * ((lam 2 (-1) : ℂˣ) : ℂ))) *
                  ∑ i, ∑ j,
                    RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          (s + 1 / 2) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                    φPS i (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ i u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) *
                      godementZeta2 p μ₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * transposeInvN (Fin 2) g)))
                (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (φ₁ i)) (lam 0)⁻¹ (s + 3 / 2))) := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI hSDH : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
    show Measure.IsAddHaarMeasure
      (((Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) •
        Measure.addHaarMeasure (integersPositiveCompacts ℚ p))
    refine Measure.IsAddHaarMeasure.nnreal_smul _ (ne_of_gt (NNReal.rpow_pos ?_))
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot)
  intro μ₂ _ μN₂ _ w₂ hw₂

  obtain ⟨K, hKo, hKc⟩ := K_standin p
  obtain ⟨U, R, hUo, h1U, hB1⟩ :=
    LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber p lam hlam σ hσ h01 h12 Φ hΦ T
  obtain ⟨h1, h2a, h2b, h3, h3', n, φ₁, φ₂₀, φPS, hφ₁, hφ₂₀, hφPS, h𝔇, h4'⟩ := hB1 μ₂ K hKo hKc _ rfl _ rfl

  set cB1 : ℂ := ((lam 1 (-1) : ℂˣ) : ℂ) with hcB1

  set W₁ : Fin n → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i k =>
      ∫ t : (p.adicCompletion ℚ), psiLocal ℚ p t * φPS i (antidiagonal2 p * upperUnipotent2 p t * k) ∂(selfDualHaarAt ℚ p)
    with hW₁
  set φ₂ : Fin n → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun i v =>
      ∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂₀ i u * psiLocal ℚ p (u.1 * v.1 + u.2 * v.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))
    with hφ₂

  set Tens : Fin n → Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ :=
    fun i X k => φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂₀ i (X 0 2, X 1 2) * W₁ i k with hTens

  set φ₁D : Fin n → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i => matFourier22 p (psiLocal ℚ p) (φ₁ i) with hφ₁D
  have hφ₁Dlc : ∀ i, IsLocallyConstant (φ₁D i) := fun i => (C3bGlueSB.matFourier22_psiLocal_lc_cs p (φ₁ i) (hφ₁ i)).1
  have hφ₁Dcs : ∀ i, HasCompactSupport (φ₁D i) := fun i => (C3bGlueSB.matFourier22_psiLocal_lc_cs p (φ₁ i) (hφ₁ i)).2

  set d₂ : GL (Fin 2) (p.adicCompletion ℚ) := diagonal2 p ![1, -1] with hd₂
  have hd₂M : ((d₂ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hd₂, diagonal2_coe]

  have hJS := fun (i : Fin n) =>
    LanglandsTunnell.CubicInduction.jacquetIntegral_principalSeries2_smooth_law_central_flip
      p ![lam 1, lam 2] (φPS i) (hφPS i).1 w₀p hw₀p d₂ hd₂M
  have hW₁lc : ∀ i, IsLocallyConstant (W₁ i) := fun i => (hJS i).2.1
  have hW₁law : ∀ i, ∀ (t : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), W₁ i (unipotent t * g) = psiLocal ℚ p (-t) * W₁ i g :=
    fun i => (hJS i).2.2.1
  have hφ₂lc : ∀ i, IsLocallyConstant (φ₂ i) := fun i => (C3bGlueSB.colPairFourier_psiLocal_lc_cs p (φ₂₀ i) (hφ₂₀ i)).1
  have hφ₂cs : ∀ i, HasCompactSupport (φ₂ i) := fun i => (C3bGlueSB.colPairFourier_psiLocal_lc_cs p (φ₂₀ i) (hφ₂₀ i)).2

  set ϖₒ : p.adicCompletionIntegers ℚ := ⟨(NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)), by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.2 (by norm_num)⟩ with hϖₒdef
  have hπₒ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖₒ ≠ 0 := by
    simpa [hϖₒdef] using (NumberField.AdelicLevel.uniformizerUnit ℚ p).ne_zero
  have hϖₒ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖₒ) = WithZero.exp (-1 : ℤ) := by
    simpa [hϖₒdef] using NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  have hVβ := AutomorphicForm.WhittakerModel.forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence
    p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral hπₒ hϖₒ

  have lc_of_sm : ∀ f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ,
      (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g) →
        IsLocallyConstant f := by
    rintro f ⟨U, hUo, hU⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(Homeomorph.mulLeft x) '' (U : Set (GL (Fin 2) (p.adicCompletion ℚ))), (Homeomorph.mulLeft x).isOpen_image.2 hUo,
      ⟨1, U.one_mem, by simp⟩, ?_⟩
    rintro y ⟨k, hk, rfl⟩
    simpa using hU k hk x
  have mem_own_span : ∀ f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ, f ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => f (g * h)) := by
    intro f
    exact Submodule.subset_span ⟨1, funext fun g => by simp⟩
  have adm_of_mem : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
        ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
          ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) := by

    have transl_mem : ∀ (h : GL (Fin 2) (p.adicCompletion ℚ)), ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)) ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := by
      intro h w hw
      have hle : (Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))).map (rightTranslate2 p h) ≤ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨_, ⟨h', rfl⟩, rfl⟩
        exact ⟨h * h', by ext g; simp [rightTranslate2_apply, mul_assoc]⟩
      have hm := hle (Submodule.mem_map_of_mem hw)
      exact hm
    intro w hw U hU
    obtain ⟨B, hB⟩ := hw₂adm U hU
    refine ⟨B, fun w' hw' hfix => hB w' ?_ hfix⟩
    refine (Submodule.span_le.2 ?_) hw'
    rintro _ ⟨h, rfl⟩
    exact transl_mem h w hw
  have hw₂sm := (hVβ w₂ hw₂).1
  have hw₂law' : ∀ (t : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), w₂ (unipotent t * g) = psiLocal ℚ p t * w₂ g := (hVβ w₂ hw₂).2.1
  have hw₂cen := (hVβ w₂ hw₂).2.2.1
  have hw₂lc : IsLocallyConstant w₂ := lc_of_sm w₂ hw₂sm
  have hw₂admS := adm_of_mem w₂ hw₂

  obtain ⟨Ω, hΩo, hΩc, hφΩ, hχΩ, hΩt⟩ :=
    OMEGA_family p (Fin n ⊕ Fin n) (Sum.elim φ₁ φ₁D)
      (by rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> first | exact hφ₁ i | exact ⟨hφ₁Dlc i, hφ₁Dcs i⟩)
      (lam 0) (hlam 0)
  have hφ₁Ω : ∀ i, ∀ ω ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      φ₁ i ((ω * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = φ₁ i ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := fun i => hφΩ (Sum.inl i)
  have hφ₁DΩ : ∀ i, ∀ ω ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      φ₁D i ((ω * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = φ₁D i ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := fun i => hφΩ (Sum.inr i)

  obtain ⟨nj, wj, ℓ, hwjV, hwjlc, hℓΩ, hclc, hsep⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_translate_eq_mul_sum_linearMap_of_admissible
      p N hN w₂base hw₂K hw₂adm μ₂ Ω hΩo hΩc w₂ hw₂
  have hwjsm := fun (j : Fin nj) => (hVβ (wj j) (hwjV j)).1
  have hwjlaw := fun (j : Fin nj) => (hVβ (wj j) (hwjV j)).2.1
  have hwjcen := fun (j : Fin nj) => (hVβ (wj j) (hwjV j)).2.2.1
  have hwjadmS := fun (j : Fin nj) => adm_of_mem (wj j) (hwjV j)

  have hDOCK := fun (i : Fin n) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
    LanglandsTunnell.CubicInduction.godementWhittaker3_iotaGL_eq_of_pureTensor p (psiLocal ℚ p)⁻¹ (lam 0)
      (φ₁ i) (φ₂₀ i) (W₁ i) (Tens i) (fun X k => rfl) μ₂ g

  have hB3 := fun (i : Fin n) (s : ℂ) =>
    LanglandsTunnell.RankinSelberg.rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta
      p (lam 0) (φ₁ i) (hφ₁ i).1 (φ₂ i) (hφ₂lc i) (W₁ i) (hW₁lc i) (hW₁law i) w₂ hw₂lc hw₂law'
      Ω hΩo hΩc (hφ₁Ω i) hχΩ (Fin nj) wj hwjlc (fun j h => ℓ j (fun x' => w₂ (x' * h))) hclc μ₂ μN₂ μ₂ hsep s

  have hμP : ∀ i, IsLocallyConstant (![lam 1, lam 2] i) := by intro i; fin_cases i <;> exact hlam _
  have hσP2 : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((![lam 1, lam 2] i a : ℂˣ) : ℂ)‖ = ‖(a : (p.adicCompletion ℚ))‖ ^ (![σ 1, σ 2] i) := by
    intro i a; fin_cases i <;> exact hσ _ a
  have h01P : ![σ 1, σ 2] 1 < ![σ 1, σ 2] 0 := h12
  have inv_lc : ∀ χ : (p.adicCompletion ℚ)ˣ →* ℂˣ, IsLocallyConstant χ → IsLocallyConstant (χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) := by
    intro χ hχ
    have h : ⇑(χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) = (fun u : ℂˣ => u⁻¹) ∘ ⇑χ := funext fun x => by simp
    rw [h]; exact hχ.comp _
  have hμD : ∀ i, IsLocallyConstant (![(lam 2)⁻¹, (lam 1)⁻¹] i) := by
    intro i; fin_cases i
    · exact inv_lc _ (hlam 2)
    · exact inv_lc _ (hlam 1)
  have inv_norm : ∀ (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℝ), (∀ a : (p.adicCompletion ℚ)ˣ, ‖((χ a : ℂˣ) : ℂ)‖ = ‖(a : (p.adicCompletion ℚ))‖ ^ t) →
      ∀ a : (p.adicCompletion ℚ)ˣ, ‖(((χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ)‖ = ‖(a : (p.adicCompletion ℚ))‖ ^ (-t) := by
    intro χ t h a
    rw [Real.rpow_neg (norm_nonneg _), ← h a]
    simp [Units.val_inv_eq_inv_val, norm_inv]
  have hσD2 : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((![(lam 2)⁻¹, (lam 1)⁻¹] i a : ℂˣ) : ℂ)‖ = ‖(a : (p.adicCompletion ℚ))‖ ^ (![-(σ 2), -(σ 1)] i) := by
    intro i a; fin_cases i
    · exact inv_norm _ _ (hσ 2) a
    · exact inv_norm _ _ (hσ 1) a
  have h01D : ![-(σ 2), -(σ 1)] 1 < ![-(σ 2), -(σ 1)] 0 := by simpa using neg_lt_neg h12
  have hχD : IsLocallyConstant ((lam 0)⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) := inv_lc _ (hlam 0)

  have hB4a := fun (i : Fin n) =>
    (LanglandsTunnell.RankinSelberg.exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
      p ![lam 1, lam 2] hμP ![σ 1, σ 2] hσP2 h01P (φPS i) (hφPS i).1 (lam 0) (hlam 0)
      (φ₁ i) (hφ₁ i) (φ₂ i) ⟨hφ₂lc i, hφ₂cs i⟩ θ₀ w₂ hw₂law' hw₂sm hw₂admS hw₂cen μ₂ μN₂ μ₂).1
  have hB4b := fun (i : Fin n) (j : Fin nj) =>
    (LanglandsTunnell.RankinSelberg.exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
      p ![lam 1, lam 2] hμP ![σ 1, σ 2] hσP2 h01P (φPS i) (hφPS i).1 (lam 0) (hlam 0)
      (φ₁ i) (hφ₁ i) (φ₂ i) ⟨hφ₂lc i, hφ₂cs i⟩ θ₀ (wj j) (hwjlaw j) (hwjsm j) (hwjadmS j) (hwjcen j) μ₂ μN₂ μ₂).2
      (wj j) (mem_own_span (wj j))
  have hGJI := fun (i : Fin n) (j : Fin nj) =>
    LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_coefficient
      p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral (lam 0) (hlam 0) μ₂ w₂ hw₂ (ℓ j) ⟨Ω, hΩo, hℓΩ j⟩
      (φ₁ i) (hφ₁ i).1 (hφ₁ i).2
  choose σa ha using hB4a
  choose σb hb using hB4b
  choose σg σgd hg using hGJI

  set σP : ℝ := (∑ i, |σa i|) + ∑ i, ∑ j, (|σb i j| + |σg i j|) with hσP
  have bound3 : ∀ (a : Fin n → ℝ) (f g : Fin n → Fin nj → ℝ) (i : Fin n) (j : Fin nj),
      a i ≤ (∑ i', |a i'|) + ∑ i', ∑ j', (|f i' j'| + |g i' j'|) ∧
      f i j ≤ (∑ i', |a i'|) + ∑ i', ∑ j', (|f i' j'| + |g i' j'|) ∧
      g i j ≤ (∑ i', |a i'|) + ∑ i', ∑ j', (|f i' j'| + |g i' j'|) := by
    intro a f g i j
    have hrow : ∀ i', 0 ≤ ∑ j', (|f i' j'| + |g i' j'|) := fun i' => Finset.sum_nonneg fun j' _ => by positivity
    have hS : 0 ≤ ∑ i', ∑ j', (|f i' j'| + |g i' j'|) := Finset.sum_nonneg fun i' _ => hrow i'
    have hA : 0 ≤ ∑ i', |a i'| := Finset.sum_nonneg fun i' _ => abs_nonneg _
    have h0 : |a i| ≤ ∑ i', |a i'| := Finset.single_le_sum (f := fun i' => |a i'|) (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
    have h1 : |f i j| + |g i j| ≤ ∑ j', (|f i j'| + |g i j'|) :=
      Finset.single_le_sum (f := fun j' => |f i j'| + |g i j'|) (fun j' _ => by positivity) (Finset.mem_univ j)
    have h2 : ∑ j', (|f i j'| + |g i j'|) ≤ ∑ i', ∑ j', (|f i' j'| + |g i' j'|) :=
      Finset.single_le_sum (f := fun i' => ∑ j', (|f i' j'| + |g i' j'|)) (fun i' _ => hrow i') (Finset.mem_univ i)
    refine ⟨?_, ?_, ?_⟩
    · linarith [le_abs_self (a i)]
    · linarith [le_abs_self (f i j), abs_nonneg (g i j)]
    · linarith [le_abs_self (g i j), abs_nonneg (f i j)]
  have haP : ∀ (i : Fin n) (s : ℂ), σP < s.re → σa i < s.re := by
    intro i s hs
    rcases nj.eq_zero_or_pos with hnj | hnj
    · have h0 : |σa i| ≤ ∑ i', |σa i'| := Finset.single_le_sum (f := fun i' => |σa i'|) (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
      have hS : 0 ≤ ∑ i', ∑ j', (|σb i' j'| + |σg i' j'|) := Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => by positivity
      linarith [le_abs_self (σa i)]
    exact lt_of_le_of_lt (bound3 σa σb σg i ⟨0, hnj⟩).1 hs
  have hbP : ∀ (i : Fin n) (j : Fin nj) (s : ℂ), σP < s.re → σb i j < s.re :=
    fun i j s hs => lt_of_le_of_lt (bound3 σa σb σg i j).2.1 hs
  have hgP : ∀ (i : Fin n) (j : Fin nj) (s : ℂ), σP < s.re → σg i j < s.re :=
    fun i j s hs => lt_of_le_of_lt (bound3 σa σb σg i j).2.2 hs

  set G : Fin n → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i g =>
    ((lam 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
      ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
        φ₁ i ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          φ₂ i (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
          W₁ i h⁻¹ * ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ₂
    with hG

  have hDOCK_G : ∀ (i : Fin n) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      godementWhittaker3 p (psiLocal ℚ p)⁻¹ μ₂ (lam 0) (Tens i) (iotaGL g) = G i g := by
    intro i g
    rw [hDOCK i g, inv_inv]

  have hW₃sum : ∀ g' : LocalGL3 p, W₃ g' = cB1 * ∑ i, godementWhittaker3 p (psiLocal ℚ p)⁻¹ μ₂ (lam 0) (Tens i) g' := by
    intro g'
    rw [hW₃]
    exact (h4' g').2
  have hW₃G : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W₃ (iotaGL g) = cB1 * ∑ i, G i g := by
    intro g
    rw [hW₃sum]
    simp only [hDOCK_G]

  have hF9 : ∀ (i : Fin n) (s : ℂ), σP < s.re →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => G i g * w₂ g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := fun i s hs =>
    LanglandsTunnell.RankinSelberg.integrable_rsIntegrand_godementSlot_of_integrable_unfold
      p (lam 0) (hlam 0) (φ₁ i) (hφ₁ i).1 (φ₂ i) (hφ₂lc i) (W₁ i) (hW₁lc i) (hW₁law i) w₂ hw₂lc hw₂law' μ₂ μN₂ μ₂ s
      (ha i s (haP i s hs))
  have hptP : ∀ (s : ℂ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) =
        ∑ i, cB1 * (G i g * w₂ g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) := by
    intro s g
    rw [hW₃G g, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint1 : ∀ s : ℂ, σP < s.re →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := by
    intro s hs
    rw [show (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) =
        fun g => ∑ i, cB1 * (G i g * w₂ g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) from funext (hptP s)]
    exact MeasureTheory.integrable_finset_sum _ fun i _ => (hF9 i s hs).const_mul cB1
  have hRSsum : ∀ s : ℂ, σP < s.re →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s (fun g => W₃ (iotaGL g)) w₂ =
        cB1 * ∑ i, RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s (G i) w₂ := by
    intro s hs
    simp only [RSCarrier.rsLocalIntegral]
    rw [show (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) =
        fun g => ∑ i, cB1 * (G i g * w₂ g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) from funext (hptP s)]
    rw [MeasureTheory.integral_finset_sum _ fun i _ => (hF9 i s hs).const_mul cB1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_const_mul]

  have hZeta : ∀ (i : Fin n) (j : Fin nj) (s : ℂ),
      (∫ h : GL (Fin 2) (p.adicCompletion ℚ),
          (fun j h => ℓ j (fun x' => w₂ (x' * h))) j h * φ₁ i (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂μ₂) =
        godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * g)))
          (φ₁ i) (lam 0) (s + 1 / 2) := by
    intro i j s
    rfl

  set d₁ : GL (Fin 2) (p.adicCompletion ℚ) := diagonal2 p ![-1, 1] with hd₁
  have hd₁M : ((d₁ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![-1, 0; 0, 1] := by
    first
      | (ext i j; fin_cases i <;> fin_cases j <;> simp [hd₁, diagonal2_coe])

  set cV : ℂ := ((θ₀ (-1) : ℂˣ) : ℂ) with hcV
  set cPS : ℂ := ((lam 1 (-1) : ℂˣ) : ℂ) * ((lam 2 (-1) : ℂˣ) : ℂ) with hcPS

  set W₁D : Fin n → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i k => W₁ i (w₀p * transposeInvN (Fin 2) k) with hW₁D
  set TensD : Fin n → Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ :=
    fun i X k => φ₁D i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * W₁D i k with hTensD

  set φ₂D : Fin n → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun i v =>
      ∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ i u * psiLocal ℚ p (u.1 * v.1 + u.2 * v.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))
    with hφ₂D
  set W₁F : Fin n → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i k => W₁ i (w₀p * transposeInvN (Fin 2) (d₂ * k)) with hW₁F

  set wF : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g => ((modulus ((Matrix.GeneralLinearGroup.det (d₂ * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) (d₂ * g)) with hwF
  set wFj : Fin nj → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun j g => ((modulus ((Matrix.GeneralLinearGroup.det (d₂ * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (w₀p * transposeInvN (Fin 2) (d₂ * g)) with hwFj
  set cF : Fin nj → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun j h => ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * transposeInvN (Fin 2) h)) with hcF

  set GD : Fin n → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i g =>
    (((lam 0)⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
      ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
        φ₁D i ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          φ₂D i (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
          W₁F i h⁻¹ * (((lam 0)⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ₂
    with hGD

  have hB2 := fun (i : Fin n) =>
    LanglandsTunnell.RankinSelberg.dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual
      p μ₂ (psiLocal ℚ p)⁻¹ (Or.inr rfl) (lam 0) w₀p hw₀p (Tens i)
      ⟨1, ![fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂₀ i (X 0 2, X 1 2)], ![W₁ i],
        (fun i₁ => by fin_cases i₁; first | exact C3bGlueSB.leftBlock_mul_lastCol_lc_cs p (φ₁ i) (φ₂₀ i) (hφ₁ i) (hφ₂₀ i) | simpa using C3bGlueSB.leftBlock_mul_lastCol_lc_cs p (φ₁ i) (φ₂₀ i) (hφ₁ i) (hφ₂₀ i)),
        (fun i₁ => by fin_cases i₁; first | exact ⟨(hJS i).2.1, (hJS i).2.2.2.1⟩ | simpa using And.intro (hJS i).2.1 (hJS i).2.2.2.1),
        by funext X k; simp [hTens]⟩

  have hTensD_eq : ∀ i : Fin n,
      (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
        matFourier23 p (psiLocal ℚ p) (fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => Tens i Y (w₀p * transposeInvN (Fin 2) k)) X) = TensD i := by
    intro i
    funext X k
    exact LanglandsTunnell.CubicInduction.matFourier23_leftBlock_mul_lastCol_mul_const p (psiLocal ℚ p) (φ₁ i) (φ₂₀ i) (W₁ i (w₀p * transposeInvN (Fin 2) k)) X

  have hGWD : ∀ (i : Fin n) (g' : LocalGL3 p),
      dualWhittakerFn3 (godementWhittaker3 p (psiLocal ℚ p)⁻¹ μ₂ (lam 0) (Tens i)) g' =
        godementWhittaker3 p (psiLocal ℚ p) μ₂ (lam 0)⁻¹ (TensD i) g' := by
    intro i g'

    have hφ0 := C3bGlueSB.leftBlock_mul_lastCol_lc_cs p (φ₁D i) (φ₂ i) ⟨hφ₁Dlc i, hφ₁Dcs i⟩ ⟨hφ₂lc i, hφ₂cs i⟩
    have h98 := LanglandsTunnell.CubicInduction.dualSection_mem_principalSeries2_and_jacquetIntegral_eq p ![lam 1, lam 2] (φPS i) (hφPS i).1 w₀p hw₀p
    have hmem : (fun Y : GL (Fin 2) (p.adicCompletion ℚ) => φPS i (w₀p * transposeInvN (Fin 2) Y)) ∈ principalSeries2 p ![(lam 2)⁻¹, (lam 1)⁻¹] := by
      simpa using h98.1
    have hGI := LanglandsTunnell.CubicInduction.integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2
      p ![(lam 2)⁻¹, (lam 1)⁻¹] hμD ![-(σ 2), -(σ 1)] hσD2 h01D _ hmem
      (fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => φ₁D i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2)) hφ0 (lam 0)⁻¹ hχD
      (psiLocal ℚ p)⁻¹ (Or.inr rfl) (psiLocal ℚ p)⁻¹ (Or.inr rfl) μ₂ g'
    have ha2 : antidiagonal2 p = w₀p := by
      apply Units.ext; rw [hw₀p]; ext a b; fin_cases a <;> fin_cases b <;> simp [antidiagonal2]
    have hu2 : ∀ x : (p.adicCompletion ℚ), upperUnipotent2 p x = unipotentGL2 x := fun x => by
      apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;> simp [upperUnipotent2, unipotentGL2]
    have hJ : ∀ k : GL (Fin 2) (p.adicCompletion ℚ),
        (∫ x : (p.adicCompletion ℚ), psiLocal ℚ p x * φPS i (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) k)) ∂(selfDualHaarAt ℚ p)) =
          ∫ x : (p.adicCompletion ℚ), (psiLocal ℚ p)⁻¹ x * φPS i (w₀p * transposeInvN (Fin 2) (antidiagonal2 p * upperUnipotent2 p x * k)) ∂(selfDualHaarAt ℚ p) := by
      intro k
      have e := (h98.2 (psiLocal ℚ p) (selfDualHaarAt ℚ p) k).2
      simp only [ha2, hu2]
      simp only [mul_comm (((psiLocal ℚ p) : (p.adicCompletion ℚ) → ℂ) _) _, mul_comm ((((psiLocal ℚ p)⁻¹ : AddChar (p.adicCompletion ℚ) ℂ) : (p.adicCompletion ℚ) → ℂ) _) _]
      exact e.symm
    have h := hB2 i g' ((h4' (longWeyl3 * transposeInv3 g')).1 i)
      (hGI.congr (Filter.Eventually.of_forall fun h => by
        have hF : (fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) =>
              φ₁D i (Matrix.of fun a b => (X * ((g' : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) a (Fin.castSucc b)) * φ₂ i ((X * ((g' : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) 0 2, (X * ((g' : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) 1 2) *
                ∫ x : (p.adicCompletion ℚ), (psiLocal ℚ p)⁻¹ x *
                  φPS i (w₀p * transposeInvN (Fin 2) (antidiagonal2 p * upperUnipotent2 p x * h⁻¹)) ∂(selfDualHaarAt ℚ p)) =
            fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => matFourier23 p (psiLocal ℚ p)⁻¹⁻¹
              (fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => Tens i Y (w₀p * transposeInvN (Fin 2) h⁻¹)) (X * ((g' : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) := by
          funext X
          rw [inv_inv]
          have t := congrFun (congrFun (hTensD_eq i) (X * ((g' : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))) h⁻¹
          rw [t]
          simp only [hTensD, hW₁D, hW₁, hJ]
        beta_reduce
        rw [hF]))
    simp only [inv_inv] at h
    rw [hTensD_eq i] at h
    exact h

  have hW₃Dsum : ∀ g' : LocalGL3 p,
      dualWhittakerFn3 W₃ g' = cB1 * ∑ i, godementWhittaker3 p (psiLocal ℚ p) μ₂ (lam 0)⁻¹ (TensD i) g' := by
    intro g'
    rw [dualWhittakerFn3_apply, hW₃sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hGWD i, dualWhittakerFn3_apply]

  have hDOCKD := fun (i : Fin n) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
    LanglandsTunnell.CubicInduction.godementWhittaker3_iotaGL_eq_of_pureTensor p (psiLocal ℚ p) (lam 0)⁻¹
      (φ₁D i) (φ₂ i) (W₁D i) (TensD i) (fun X k => rfl) μ₂ g
  have hGD_eq : ∀ (i : Fin n) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      godementWhittaker3 p (psiLocal ℚ p) μ₂ (lam 0)⁻¹ (TensD i) (iotaGL (d₂ * g)) = GD i g := by
    intro i g
    rw [hDOCKD i (d₂ * g)]
    exact LanglandsTunnell.CubicInduction.godementDock_diagFlip_eq p (psiLocal ℚ p) (lam 0)⁻¹ (φ₁D i) (φ₂ i) (W₁D i) d₂ hd₂M μ₂ g

  have hφ₂Dlc : ∀ i, IsLocallyConstant (φ₂D i) := fun i => (C3bGlueSB.colPairFourier_psiLocal_lc_cs p (φ₂ i) ⟨hφ₂lc i, hφ₂cs i⟩).1
  have hφ₂Dcs : ∀ i, HasCompactSupport (φ₂D i) := fun i => (C3bGlueSB.colPairFourier_psiLocal_lc_cs p (φ₂ i) ⟨hφ₂lc i, hφ₂cs i⟩).2
  have hW₁Flc : ∀ i, IsLocallyConstant (W₁F i) := fun i => (hJS i).2.2.2.2.2.2
  have hW₁Flaw : ∀ i, ∀ (t : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), W₁F i (unipotent t * g) = psiLocal ℚ p (-t) * W₁F i g :=
    fun i => (hJS i).2.2.2.2.2.1

  have hP := LanglandsTunnell.RankinSelberg.dualPartner_block_of_admissible
    p θ₀ N hN w₂base hw₂law hw₂K hw₂adm hcentral w₀p hw₀p d₂ hd₂M w₂ hw₂
  have hPj := fun (j : Fin nj) => LanglandsTunnell.RankinSelberg.dualPartner_block_of_admissible
    p θ₀ N hN w₂base hw₂law hw₂K hw₂adm hcentral w₀p hw₀p d₂ hd₂M (wj j) (hwjV j)
  have hwFlc : IsLocallyConstant wF := hP.1
  have hwFlaw : ∀ (t : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), wF (unipotent t * g) = psiLocal ℚ p t * wF g := hP.2.1
  have hχΩD : ∀ ω ∈ Ω, (lam 0)⁻¹ (Matrix.GeneralLinearGroup.det ω) = 1 := by
    intro ω hω
    simp [hχΩ ω hω]
  have hwFjlc : ∀ j, IsLocallyConstant (wFj j) := fun j => (hPj j).1
  have hTcont : Continuous (fun g : GL (Fin 2) (p.adicCompletion ℚ) => transposeInvN (Fin 2) g) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · simp only [Function.comp_def, coe_transposeInvN]
      exact (Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).matrix_transpose
    · simp only [← Matrix.coe_units_inv, coe_inv_transposeInvN]
      exact (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).matrix_transpose
  have hcFlc : ∀ j, IsLocallyConstant (cF j) := fun j =>
    (C3bGlueQ.isLocallyConstant_modulus_det p).comp₂ ((hclc j).comp_continuous hTcont) (· * ·)

  have hφdual := fun (i : Fin n) =>
    LanglandsTunnell.CubicInduction.conj_transposeInvN_mem_principalSeries2 p ![lam 1, lam 2] (φPS i) (hφPS i).1 w₀p hw₀p
  set φflat : Fin n → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i Y => φPS i (w₀p * transposeInvN (Fin 2) (Y * w₀p) * w₀p) with hφflat
  have hφflat_mem : ∀ i, φflat i ∈ principalSeries2 p ![(lam 2)⁻¹, (lam 1)⁻¹] := by
    intro i
    first
      | (have h__af := rightTranslate2_mem_principalSeries2 (hφdual i) w₀p; simp [rightTranslate2_apply] at h__af; exact h__af)
  have hJW := fun (i : Fin n) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
    LanglandsTunnell.CubicInduction.integral_psiLocal_mul_transposeInvN_eq_mul_integral_psiLocal_mul_dual
      p ![lam 1, lam 2] (φPS i) (hφPS i).1 w₀p hw₀p (d₂ * k)
  set cJW : ℂ := ((lam 2 (-1) : ℂˣ) : ℂ) with hcJW
  have hW₁F_flat : ∀ (i : Fin n) (k : GL (Fin 2) (p.adicCompletion ℚ)),
      W₁F i k = cJW * ∫ x : (p.adicCompletion ℚ), psiLocal ℚ p x * φflat i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p) := by

    have hd2sq : d₂ * d₂ = 1 := by
      apply Units.ext
      rw [Units.val_mul, hd₂M, Units.val_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    intro i k
    have h := hJW i k
    have hk : diagonal2 p ![1, -1] * (d₂ * k) * w₀p = k * w₀p := by
      rw [← mul_assoc, (show diagonal2 p ![1, -1] * d₂ = 1 from hd2sq), one_mul]
    have e : ∀ x : (p.adicCompletion ℚ),
        φPS i (w₀p * transposeInvN (Fin 2) (antidiagonal2 p * upperUnipotent2 p x * (diagonal2 p ![1, -1] * (d₂ * k) * w₀p)) * w₀p) =
          φflat i (antidiagonal2 p * upperUnipotent2 p x * k) := by
      intro x
      rw [hk, ← mul_assoc]
    simp only [hW₁F, hW₁]
    rw [h]
    simp only [e, hcJW, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_fin_one]

  obtain ⟨θF, hwFcentral⟩ := hP.2.2.2.2.1
  have hwFsm := hP.2.2.1
  have hwFadm := hP.2.2.2.1
  have hθj := fun (j : Fin nj) => (hPj j).2.2.2.2.1
  choose θFj hθFj using hθj
  have hB4Da := fun (i : Fin n) =>
    (LanglandsTunnell.RankinSelberg.exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
      p ![(lam 2)⁻¹, (lam 1)⁻¹] hμD ![-(σ 2), -(σ 1)] hσD2 h01D (φflat i) (hφflat_mem i) (lam 0)⁻¹ hχD
      (φ₁D i) ⟨hφ₁Dlc i, hφ₁Dcs i⟩ (φ₂D i) ⟨hφ₂Dlc i, hφ₂Dcs i⟩ θF wF hwFlaw hwFsm hwFadm hwFcentral μ₂ μN₂ μ₂).1
  have hB4Db := fun (i : Fin n) (j : Fin nj) =>
    (LanglandsTunnell.RankinSelberg.exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
      p ![(lam 2)⁻¹, (lam 1)⁻¹] hμD ![-(σ 2), -(σ 1)] hσD2 h01D (φflat i) (hφflat_mem i) (lam 0)⁻¹ hχD
      (φ₁D i) ⟨hφ₁Dlc i, hφ₁Dcs i⟩ (φ₂D i) ⟨hφ₂Dlc i, hφ₂Dcs i⟩ (θFj j) (wFj j) (hPj j).2.1 (hPj j).2.2.1 (hPj j).2.2.2.1 (hθFj j)
      μ₂ μN₂ μ₂).2 (wFj j) (mem_own_span (wFj j))
  choose σad had using hB4Da
  choose σbd hbd using hB4Db
  set σD : ℝ := (∑ i, |σad i|) + ∑ i, ∑ j, (|σbd i j| + |σgd i j|) with hσD
  have haD : ∀ (i : Fin n) (s : ℂ), σD < s.re → σad i < s.re := by
    intro i s hs
    rcases nj.eq_zero_or_pos with hnj | hnj
    · have h0 : |σad i| ≤ ∑ i', |σad i'| := Finset.single_le_sum (f := fun i' => |σad i'|) (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
      have hS : 0 ≤ ∑ i', ∑ j', (|σbd i' j'| + |σgd i' j'|) := Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => by positivity
      linarith [le_abs_self (σad i)]
    exact lt_of_le_of_lt (bound3 σad σbd σgd i ⟨0, hnj⟩).1 hs
  have hbD : ∀ (i : Fin n) (j : Fin nj) (s : ℂ), σD < s.re → σbd i j < s.re :=
    fun i j s hs => lt_of_le_of_lt (bound3 σad σbd σgd i j).2.1 hs
  have hgD : ∀ (i : Fin n) (j : Fin nj) (s : ℂ), σD < s.re → σgd i j < s.re :=
    fun i j s hs => lt_of_le_of_lt (bound3 σad σbd σgd i j).2.2 hs

  obtain ⟨hSC, hLCo, hN₂cl, hRinv⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hSC
  haveI := hLCo
  haveI : μN₂.IsMulRightInvariant := hRinv μN₂
  have hδN := C3bGlueQ.modulus_det_unipotent_mul p
  have hd₂N := C3bGlueQ.mem_range_unipotentGL2Hom_iff_conj p ![1, -1]
  have hd₂μ := C3bGlueQ.lintegral_comp_conj_diagonal2_eq p ![1, -1] (by simp) μN₂
  have hδd₂ := C3bGlueQ.modulus_det_diagonal2_mul p ![1, -1] (by simp)
  have hd₁N := C3bGlueQ.mem_range_unipotentGL2Hom_iff_conj p ![-1, 1]
  have hd₁μ := C3bGlueQ.lintegral_comp_conj_diagonal2_eq p ![-1, 1] (by simp) μN₂
  have hδd₁ := C3bGlueQ.modulus_det_diagonal2_mul p ![-1, 1] (by simp)

  have hd2sq : d₂ * d₂ = 1 := by
    apply Units.ext
    rw [Units.val_mul, hd₂M, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hd2g : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), d₂ * (d₂ * g) = g := fun g => by rw [← mul_assoc, hd2sq, one_mul]

  have H1D := fun (i : Fin n) (s : ℂ) (hs : σD < s.re) => ((had i s (haD i s hs)).const_mul cJW)
  have H2D := fun (i : Fin n) (j : Fin nj) (s : ℂ) (hs : σD < s.re) => ((hbd i j s (hbD i j s hs)).const_mul cJW)
  have H3D := fun (i : Fin n) (j : Fin nj) (s : ℂ) (hs : σD < s.re) => (hg i j).2 s (hgD i j s hs)
  have hpowD : ∀ (h : GL (Fin 2) (p.adicCompletion ℚ)) (s : ℂ), ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2) = ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) := by
    intro h s
    have hx : ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos (Units.ne_zero _)).ne'
    rw [show s + 3 / 2 = 1 + (s + 1 / 2) by ring, Complex.cpow_add _ _ hx, Complex.cpow_one]
  have hF9D : ∀ (i : Fin n) (s : ℂ), σD < s.re →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => GD i g * wF g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := fun i s hs =>
    LanglandsTunnell.RankinSelberg.integrable_rsIntegrand_godementSlot_of_integrable_unfold
      p (lam 0)⁻¹ hχD (φ₁D i) (hφ₁Dlc i) (φ₂D i) (hφ₂Dlc i) (W₁F i) (hW₁Flc i) (hW₁Flaw i) wF hwFlc hwFlaw μ₂ μN₂ μ₂ s
      ((H1D i s hs).congr (Filter.Eventually.of_forall fun gh => by simp only [hW₁F_flat]; ring))
  have hptD : ∀ (s : ℂ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ((cB1 * ∑ i, GD i g) * wF g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) =
        ∑ i, cB1 * (GD i g * wF g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) := by
    intro s g
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hintTr : ∀ s : ℂ, σD < s.re →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((cB1 * ∑ i, GD i g) * wF g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := by
    intro s hs
    rw [show (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((cB1 * ∑ i, GD i g) * wF g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) =
        fun g => ∑ i, cB1 * (GD i g * wF g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) from funext (hptD s)]
    exact MeasureTheory.integrable_finset_sum _ fun i _ => (hF9D i s hs).const_mul cB1

  have hintD : ∀ s : ℂ, σD < s.re →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) := by
    intro s hs
    have hq := (RSCarrier.integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq
      μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range hN₂cl μN₂ d₂ hd₂N hd₂μ
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ)) hδN hδd₂ s
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 W₃ (iotaGL (d₂ * g))) wF
      (by
        intro h hh g
        have hq7 := C3bGlueQ.dual_pair_unipotent_invariant p lam hlam Φ hΦ T W₃ hW₃ w₂ hw₂law' w₀p hw₀p
          (d₂ * h * d₂⁻¹) ((hd₂N h).1 hh) (d₂ * g)
        have e1 : d₂ * h * d₂⁻¹ * (d₂ * g) = d₂ * (h * g) := by group
        simp only [e1, hwF] at hq7 ⊢
        exact hq7)
      (C3bGlueQ.measurable_rsIntegrand p _ _
        ((C3bGlueQ.isLocallyConstant_jacquetWhittaker3_iotaGL_and_dual p lam hlam Φ hΦ T W₃ hW₃).2.comp_continuous
          (continuous_mul_left d₂)) hwFlc s)
      ((hintTr s hs).congr (Filter.Eventually.of_forall fun g => by simp only [hW₃Dsum, hGD_eq]))).1
    refine hq.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [hwF, hd2g]

  have hQT32 := fun (s : ℂ) (hs : σD < s.re) =>
    (RSCarrier.integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq
      μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range hN₂cl μN₂ d₂ hd₂N hd₂μ
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ)) hδN hδd₂ s
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 W₃ (iotaGL g))
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g))
      (C3bGlueQ.dual_pair_unipotent_invariant p lam hlam Φ hΦ T W₃ hW₃ w₂ hw₂law' w₀p hw₀p)
      (C3bGlueQ.measurable_rsIntegrand p _ _
        (C3bGlueQ.isLocallyConstant_jacquetWhittaker3_iotaGL_and_dual p lam hlam Φ hΦ T W₃ hW₃).2
        (by
          have e : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) = wF ∘ (fun g => d₂ * g) := by
            funext g; simp only [Function.comp, hwF, hd2g]
          rw [e]; exact hwFlc.comp_continuous (continuous_mul_left d₂)) s)
      (hintD s hs)).2

  have hsepF : ∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
      ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), wF (g * ω * h) ∂μ₂ =
        ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, cF j h * wFj j g :=
    LanglandsTunnell.RankinSelberg.setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
      p Ω hΩc hΩt w₂ (Fin nj) wj (fun j h => ℓ j (fun x' => w₂ (x' * h))) w₀p d₂ μ₂ hsep

  have hB3D := fun (i : Fin n) (s : ℂ) =>
    LanglandsTunnell.RankinSelberg.rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta
      p (lam 0)⁻¹ (φ₁D i) (hφ₁Dlc i) (φ₂D i) (hφ₂Dlc i) (W₁F i) (hW₁Flc i) (hW₁Flaw i) wF hwFlc hwFlaw
      Ω hΩo hΩc (hφ₁DΩ i) hχΩD (Fin nj) wFj hwFjlc cF hcFlc μ₂ μN₂ μ₂ hsepF s

  have hZetaD : ∀ (i : Fin n) (j : Fin nj) (s : ℂ),
      (∫ h : GL (Fin 2) (p.adicCompletion ℚ),
          cF j h * φ₁D i (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (((lam 0)⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂μ₂) =
        godementZeta2 p μ₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ℓ j (fun x' : GL (Fin 2) (p.adicCompletion ℚ) => w₂ (x' * transposeInvN (Fin 2) g)))
          (matFourier22 p (psiLocal ℚ p) (φ₁ i)) (lam 0)⁻¹ (s + 3 / 2) := by
    intro i j s
    rw [godementZeta2_apply]
    refine congrArg (fun f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ => ∫ h, f h ∂μ₂) (funext fun h => ?_)
    simp only [hcF, hφ₁D]
    have hx : ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (modulus_pos (Units.ne_zero _)).ne'
    have hpow : ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2) = ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) := by
      rw [show s + 3 / 2 = 1 + (s + 1 / 2) by ring, Complex.cpow_add _ _ hx, Complex.cpow_one]
    rw [hpow]
    ring

  have hneg1 : d₂ * d₁ = Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) := by
    apply Units.ext
    rw [Units.val_mul, hd₂M, hd₁M]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  have hTz : transposeInvN (Fin 2) (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : (p.adicCompletion ℚ)ˣ)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) := by
    apply Units.ext
    rw [coe_transposeInvN, ← map_inv, inv_neg_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]
  have hTd : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), transposeInvN (Fin 2) (d₂ * (d₁ * g)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * transposeInvN (Fin 2) g := by
    intro g
    rw [← mul_assoc, hneg1, transposeInvN_mul, hTz]
  have hzw : ∀ X : GL (Fin 2) (p.adicCompletion ℚ), w₀p * (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * X) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * (w₀p * X) := by
    intro X
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, hw₀p, Matrix.mul_apply, Fin.sum_univ_two]
  have hδd₂' : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (modulus ((Matrix.GeneralLinearGroup.det (d₂ * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) = (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) := hδd₂
  have hδd₁' : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (modulus ((Matrix.GeneralLinearGroup.det (d₁ * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) = (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) := hδd₁
  have hW₁Fd₁ : ∀ (i : Fin n) (g : GL (Fin 2) (p.adicCompletion ℚ)), W₁F i (d₁ * g) = cPS * W₁ i (w₀p * transposeInvN (Fin 2) g) := by
    intro i g
    have h3 := (hJS i).2.2.2.2.1 (-1) (w₀p * transposeInvN (Fin 2) g)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h3
    simp only [hW₁F, hW₁, hTd, hzw]
    rw [h3, hcPS]
  have hwFjd₁ : ∀ (j : Fin nj) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      wFj j (d₁ * g) = cV * (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (w₀p * transposeInvN (Fin 2) g)) := by
    intro j g
    simp only [hwFj]
    rw [hδd₂', hδd₁', hTd, hzw, (hPj j).2.2.2.2.2, hcV]
    ring
  have hrow0 : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (((d₁ * g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 := by
    intro g; rw [Units.val_mul, hd₁M]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrow1 : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (((d₁ * g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 := by
    intro g; rw [Units.val_mul, hd₁M]; simp [Matrix.mul_apply, Fin.sum_univ_two]

  have hrowc : Continuous (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) :=
    (Units.continuous_val.matrix_elem 1 0).prodMk (Units.continuous_val.matrix_elem 1 1)
  have hQ22 := fun (i : Fin n) (j : Fin nj) (s : ℂ) (hs : σD < s.re) =>
    RSCarrier.integrable_and_rsLocalIntegral_mul_left_eq_of_forall_lintegral_conj_eq
      μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range hN₂cl μN₂ d₁ hd₁N hd₁μ
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ)) hδN hδd₁ (s + 1 / 2)
      (W₁F i) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => wFj j g * φ₂D i (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))
      (C3bGlueQ.pair22_unipotent_invariant p (W₁F i) (wFj j) (φ₂D i) (hW₁Flaw i) (hPj j).2.1)
      (C3bGlueQ.measurable_rsIntegrand p (W₁F i) _ (hW₁Flc i)
        ((hwFjlc j).comp₂ ((hφ₂Dlc i).comp_continuous hrowc) (· * ·)) (s + 1 / 2))
      ((H2D i j s hs).congr (Filter.Eventually.of_forall fun g => by simp only [hW₁F_flat]; ring))
  have h22D : ∀ (i : Fin n) (j : Fin nj) (s : ℂ), σD < s.re →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          (s + 1 / 2) (W₁F i) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => wFj j g * φ₂D i (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) =
        (cPS * cV) *
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          (s + 1 / 2) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                  φPS i (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
                    wj j (w₀p * transposeInvN (Fin 2) g) *
                  (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ i u *
                    NumberField.StandardAddChar.psiLocal ℚ p
                      (u.1 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                  ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) := by
    intro i j s hs
    have q := (hQ22 i j s hs).2
    rw [← q]
    have e1 : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₁F i (d₁ * g)) = fun g => cPS * W₁ i (w₀p * transposeInvN (Fin 2) g) :=
      funext (hW₁Fd₁ i)
    have e2 : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) => wFj j g * φ₂D i (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) (d₁ * g)) =
        fun g => cV * (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (w₀p * transposeInvN (Fin 2) g) * φ₂D i (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) := by
      funext g
      simp only []
      rw [hwFjd₁ j g, hrow0 g, hrow1 g]
      ring
    rw [e1, e2, C3bGlue.rsLocalIntegral_const_mul]

  have hRSDsum : ∀ s : ℂ, σD < s.re →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s (fun g : GL (Fin 2) (p.adicCompletion ℚ) => cB1 * ∑ i, GD i g) wF =
        cB1 * ∑ i, RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s (GD i) wF := by
    intro s hs
    simp only [RSCarrier.rsLocalIntegral]
    rw [show (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((cB1 * ∑ i, GD i g) * wF g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) =
        fun g => ∑ i, cB1 * (GD i g * wF g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) from funext (hptD s)]
    rw [MeasureTheory.integral_finset_sum _ fun i _ => (hF9D i s hs).const_mul cB1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_const_mul]

  refine ⟨n, nj, φPS, φ₁, φ₂, wj, ℓ, cB1, σP, σD, ?hc0, fun i => (hφPS i).1, hφ₁, fun i => ⟨hφ₂lc i, hφ₂cs i⟩, hwjV,
    fun j => ⟨Ω, hΩo, hℓΩ j⟩, ?prim, ?dual⟩
  case hc0 => exact Units.ne_zero _
  case prim =>
    intro s hs
    refine ⟨?int1, fun i j => ⟨?int22, ?intGJ⟩, ?idP⟩
    case int1 => exact hint1 s hs
    case int22 => exact hb i j s (hbP i j s hs)
    case intGJ => exact (hg i j).1 s (hgP i j s hs)
    case idP =>
      rw [hRSsum s hs]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hB3 i s (ha i s (haP i s hs)) (fun j => hb i j s (hbP i j s hs)) (fun j => (hg i j).1 s (hgP i j s hs))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hZeta i j s]
  case dual =>
    intro s hs
    refine ⟨?int1d, fun i j => ⟨?int22d, ?intGJd⟩, ?idD⟩
    case int1d => exact hintD s hs
    case int22d =>
      have hk : cPS * cV ≠ 0 :=
        mul_ne_zero (by rw [hcPS]; exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (by rw [hcV]; exact Units.ne_zero _)
      have hI := ((hQ22 i j s hs).1).const_mul ((cPS * cV)⁻¹)
      refine hI.congr (Filter.Eventually.of_forall fun g => ?_)
      dsimp only
      rw [hW₁Fd₁, hwFjd₁, hrow0, hrow1]
      rw [show ∀ (A B C δ : ℂ), (cPS * cV)⁻¹ * (cPS * A * (cV * B * C) * δ) = ((cPS * cV)⁻¹ * (cPS * cV)) * (A * (B * C) * δ)
        from fun A B C δ => by ring, inv_mul_cancel₀ hk, one_mul]
    case intGJd => exact (hg i j).2 s (hgD i j s hs)
    case idD =>

      rw [← hQT32 s hs]
      have eW : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 W₃ (iotaGL g)) (d₂ * g)) =
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => cB1 * ∑ i, GD i g := by
        funext g
        simp only []
        rw [hW₃Dsum]
        simp only [hGD_eq]
      have eF : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) (d₂ * g)) = wF := by
        funext g
        rfl
      rw [eW, eF, hRSDsum s hs]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hB3D i s ((H1D i s hs).congr (Filter.Eventually.of_forall fun gh => by simp only [hW₁F_flat]; ring))
        (fun j => (H2D i j s hs).congr (Filter.Eventually.of_forall fun g => by simp only [hW₁F_flat]; ring))
        (fun j => (H3D i j s hs).congr (Filter.Eventually.of_forall fun h => by simp only [hcF, hφ₁D, hpowD]; ring)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h22D i j s hs, hZetaD i j s, hcPS, hcV]
      ring

end

end S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2 (solution)
