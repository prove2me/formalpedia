-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7dca03a2-a271-5813-b527-103da1c20121

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
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
import Theorems.Thm_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.modulus_coe_units TateLocal.modulus_mul TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace RankinSelberg
namespace UnfoldGodement32
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

section Aux

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem isLocallyConstant_chi_det (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hχΩ : ∀ ω ∈ Ω, χ (Matrix.GeneralLinearGroup.det ω) = 1) :
    IsLocallyConstant (fun h : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)) := by
  intro sset
  rw [isOpen_iff_mem_nhds]
  intro h hh
  have hU : IsOpen {k : GL (Fin 2) (p.adicCompletion ℚ) | k * h⁻¹ ∈ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))} :=
    hΩo.preimage (continuous_id.mul continuous_const)
  have hmem : h ∈ {k : GL (Fin 2) (p.adicCompletion ℚ) | k * h⁻¹ ∈ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))} := by
    simp only [Set.mem_setOf_eq, mul_inv_cancel, SetLike.mem_coe]
    exact Ω.one_mem
  refine Filter.mem_of_superset (hU.mem_nhds hmem) ?_
  intro k hk
  simp only [Set.mem_setOf_eq, SetLike.mem_coe] at hk
  simp only [Set.mem_preimage] at hh ⊢
  have hdet : χ (Matrix.GeneralLinearGroup.det k) = χ (Matrix.GeneralLinearGroup.det h) := by
    have h1 := hχΩ _ hk
    rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  rw [hdet]
  exact hh

theorem modulus_det_eq_one_of_mem (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))) :
    ∀ ω ∈ Ω, (modulus ((Matrix.GeneralLinearGroup.det ω : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) = 1 := by

  have hf : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) =
      ‖((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ := fun g => by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
    rfl
  have hcont : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => ‖((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ := by
    refine continuous_norm.comp ?_
    have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) =
        fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det := by
      funext g; rfl
    rw [this]
    exact Units.continuous_val.matrix_det
  obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn hcont.continuousOn

  have hle : ∀ ω ∈ Ω, ∀ n : ℕ, ‖((Matrix.GeneralLinearGroup.det ω : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ n ≤ C := by
    intro ω hω n
    have h1 := hC (ω ^ n) (Ω.pow_mem hω n)
    rw [Real.norm_of_nonneg (norm_nonneg _), map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
    exact h1
  intro ω hω
  rw [hf]
  have hpos : 0 < ‖((Matrix.GeneralLinearGroup.det ω : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ := norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det ω).ne_zero
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    have hinv : ‖((Matrix.GeneralLinearGroup.det ω⁻¹ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ =
        ‖((Matrix.GeneralLinearGroup.det ω : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖⁻¹ := by
      rw [map_inv, Units.val_inv_eq_inv_val, norm_inv]
    have hgt' : 1 < ‖((Matrix.GeneralLinearGroup.det ω⁻¹ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ := by
      rw [hinv]; exact one_lt_inv₀ hpos |>.mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hgt'
    exact absurd (hle ω⁻¹ (Ω.inv_mem hω) n) (not_le.mpr hn)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hgt
    exact absurd (hle ω hω n) (not_le.mpr hn)

theorem cpow_bookkeeping (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    (a : ℂ) * ((a : ℂ) * (b : ℂ))⁻¹ ^ (1 / 2 : ℂ) * (a : ℂ) ^ (s - 1 / 2) =
      ((b : ℂ)⁻¹) ^ (s + 1 / 2) * ((a : ℂ) * (b : ℂ)) ^ s := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hargb : (b : ℂ).arg ≠ Real.pi := by rw [Complex.arg_ofReal_of_nonneg hb.le]; exact Real.pi_ne_zero.symm
  have hargab : ((a : ℂ) * b).arg ≠ Real.pi := by
    rw [← Complex.ofReal_mul, Complex.arg_ofReal_of_nonneg (mul_pos ha hb).le]; exact Real.pi_ne_zero.symm
  rw [Complex.inv_cpow _ _ hargab, Complex.inv_cpow _ _ hargb,
    Complex.mul_cpow_ofReal_nonneg ha.le hb.le, Complex.mul_cpow_ofReal_nonneg ha.le hb.le]
  rw [Complex.cpow_sub _ _ ha0, Complex.cpow_add _ _ hb0]
  have h1 : (a : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr ha0
  have h2 : (b : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hb0
  have h3 : (b : ℂ) ^ s ≠ 0 := fun h => hb0 (Complex.cpow_eq_zero_iff _ _ |>.mp h).1
  have h4 : (a : ℂ) ^ (1 / 2 : ℂ) * (a : ℂ) ^ (1 / 2 : ℂ) = a := by
    rw [← Complex.cpow_add _ _ ha0]; norm_num
  field_simp
  linear_combination (-(a : ℂ) ^ s) * h4

theorem chi_cancel (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (g k : GL (Fin 2) (p.adicCompletion ℚ)) :
    ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det ((g * k)⁻¹)) : ℂˣ) : ℂ) = ((χ (Matrix.GeneralLinearGroup.det (k⁻¹)) : ℂˣ) : ℂ) := by
  rw [← Units.val_mul, ← map_mul]
  congr 2
  rw [map_inv, map_mul, map_inv, mul_inv_rev, mul_comm ((Matrix.GeneralLinearGroup.det k)⁻¹), ← mul_assoc,
    mul_inv_cancel, one_mul]

theorem modulus_cancel (g k : GL (Fin 2) (p.adicCompletion ℚ)) (s : ℂ) :
    ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det ((g * k)⁻¹) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) =
      ((modulus ((Matrix.GeneralLinearGroup.det (k⁻¹) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) * ((modulus ((Matrix.GeneralLinearGroup.det (g * k) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s := by
  simp only [LanglandsTunnell.TateLocal.modulus_coe_units, map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv]
  push_cast
  exact cpow_bookkeeping _ _ (NNReal.coe_pos.mpr MeasureTheory.distribHaarChar_pos)
    (NNReal.coe_pos.mpr MeasureTheory.distribHaarChar_pos) s

theorem modulusR_det_eq_norm (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) = ‖((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
  rfl

theorem continuous_modulusR_det : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) := by
  have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ)) =
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ := by
    funext g; rw [modulusR_det_eq_norm]; rfl
  rw [this]
  exact continuous_norm.comp Units.continuous_val.matrix_det

theorem measurable_weight' {G' : Type*} [Group G'] [TopologicalSpace G'] [MeasurableSpace G'] [BorelSpace G']
    (H : Subgroup G') (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · simp_rw [ENNReal.tsum_eq_iSup_sum]
    refine Measurable.iSup fun s => s.measurable_fun_sum fun n _ => ?_
    exact measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet))
  · exact measurable_const

theorem measurable_density' {G' : Type*} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G']
    (H : Subgroup G') (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight' H μH
  have h2 : Measurable fun z : G' × H => HaarQuotient.weight H μH ((z.2 : G') * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

theorem unipotent_eq_unipotentGL2 (y : (p.adicCompletion ℚ)) :
    (unipotent y : GL (Fin 2) (p.adicCompletion ℚ)) = unipotentGL2 y := Units.ext rfl

theorem det_unipotentGL2 (y : (p.adicCompletion ℚ)) : Matrix.GeneralLinearGroup.det (unipotentGL2 y : GL (Fin 2) (p.adicCompletion ℚ)) = 1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem unipotentGL2_mul_apply_one (y : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) (j : Fin 2) :
    ((unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j = (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end Aux

section Steps

variable (p : HeightOneSpectrum (𝓞 ℚ))

noncomputable def kB (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
    (W₁ w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (s : ℂ) (g h : GL (Fin 2) (p.adicCompletion ℚ)) : ℂ :=
  ((φ₁ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
            (W₁ g * w (g * h) * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))

variable (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
    (W₁ w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (s : ℂ)

theorem kB_apply (g h : GL (Fin 2) (p.adicCompletion ℚ)) : kB p χ φ₁ φ₂ W₁ w s g h = ((φ₁ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
            (W₁ g * w (g * h) * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s)) := rfl

theorem S1_pointwise (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    ((((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
              ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
                φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  φ₂ (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  W₁ h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν) * w g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) =
      ∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (g * k) (k⁻¹) ∂ν := by
  simp only [kB_apply]
  have hsub : (∫ h : GL (Fin 2) (p.adicCompletion ℚ), φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                φ₂ (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                W₁ h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν) =
      ∫ k : GL (Fin 2) (p.adicCompletion ℚ), φ₁ (((g * k)⁻¹ * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                φ₂ (((((g * k)⁻¹)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((((g * k)⁻¹)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                W₁ ((g * k)⁻¹)⁻¹ * ((χ (Matrix.GeneralLinearGroup.det ((g * k)⁻¹)) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det ((g * k)⁻¹) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν := by
    calc (∫ h : GL (Fin 2) (p.adicCompletion ℚ), φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                φ₂ (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                W₁ h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν)
        = ∫ h : GL (Fin 2) (p.adicCompletion ℚ), φ₁ ((h⁻¹ * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                φ₂ ((((h⁻¹)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (((h⁻¹)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                W₁ (h⁻¹)⁻¹ * ((χ (Matrix.GeneralLinearGroup.det (h⁻¹)) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det (h⁻¹) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν :=
          (integral_inv_eq_self (fun h : GL (Fin 2) (p.adicCompletion ℚ) => φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                φ₂ (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                W₁ h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ν).symm
      _ = ∫ k : GL (Fin 2) (p.adicCompletion ℚ), φ₁ (((g * k)⁻¹ * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                φ₂ (((((g * k)⁻¹)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((((g * k)⁻¹)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                W₁ ((g * k)⁻¹)⁻¹ * ((χ (Matrix.GeneralLinearGroup.det ((g * k)⁻¹)) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det ((g * k)⁻¹) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν :=
          (integral_mul_left_eq_self (fun h : GL (Fin 2) (p.adicCompletion ℚ) => φ₁ ((h⁻¹ * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                φ₂ ((((h⁻¹)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (((h⁻¹)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                W₁ (h⁻¹)⁻¹ * ((χ (Matrix.GeneralLinearGroup.det (h⁻¹)) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det (h⁻¹) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) g).symm
  rw [hsub, ← integral_const_mul, ← integral_mul_const, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ (fun k => ?_))
  beta_reduce
  have g1 : (g * k)⁻¹ * g = k⁻¹ := by rw [mul_inv_rev, inv_mul_cancel_right]
  have g2 : ((g * k)⁻¹)⁻¹ = g * k := inv_inv _
  have g3 : g * k * k⁻¹ = g := mul_inv_cancel_right g k
  rw [g1, g2, g3]
  have hboth := congr (congrArg (· * ·) (chi_cancel p χ g k)) (modulus_cancel p g k s)
  linear_combination (φ₁ ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * φ₂ (((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) * W₁ (g * k) * w g) * hboth

theorem S3_average [SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))] [LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ))]
    (hφ₁ : IsLocallyConstant φ₁) (hw : IsLocallyConstant w)
    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))) (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hφ₁Ω : ∀ ω ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      φ₁ ((ω * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = φ₁ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
    (hχΩ : ∀ ω ∈ Ω, χ (Matrix.GeneralLinearGroup.det ω) = 1)
    {ι : Type} [Fintype ι] (wj : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (c : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure]
    (hsep : ∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g * ω * h) ∂ν =
          ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, c j h * wj j g)
    (hH3 : ∀ j, Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) ν)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) (hBg : Integrable (fun k : GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s g k) ν) :
    ∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂ν = ∑ j, ((W₁ g * (wj j g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) * (∫ h : GL (Fin 2) (p.adicCompletion ℚ), c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν) := by
  have hΩm : MeasurableSet (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩo.measurableSet
  have hΩpos : 0 < ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩo.measure_pos ν ⟨1, Ω.one_mem⟩
  have hΩfin : ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) < ⊤ := hΩc.measure_lt_top
  have hΩreal : ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hΩpos.ne' hΩfin.ne).ne'

  have hφ₁m : Measurable fun m : GL (Fin 2) (p.adicCompletion ℚ) => φ₁ (m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    (hφ₁.continuous.comp Units.continuous_val).measurable
  have hχm : Measurable fun h : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) :=
    (isLocallyConstant_chi_det p χ Ω hΩo hχΩ).continuous.measurable
  have hdm : Measurable fun h : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp (continuous_modulusR_det p)).measurable
  have hwm : Measurable w := hw.continuous.measurable
  have hFm : Measurable fun k : GL (Fin 2) (p.adicCompletion ℚ) => (φ₁ ((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) := (hφ₁m.mul hχm).mul (hdm.pow_const _)
  have hBm : Measurable fun k : GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s g k := by
    simp only [kB_apply]; exact
    hFm.mul (((measurable_const.mul (hwm.comp (measurable_const_mul g))).mul measurable_const).mul
      measurable_const)

  have hinv : ∀ ω ∈ Ω, ∀ k : GL (Fin 2) (p.adicCompletion ℚ),
      kB p χ φ₁ φ₂ W₁ w s g (ω * k) = (φ₁ ((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) * (W₁ g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s) * w (g * ω * k) := by
    intro ω hω k
    have h1 : φ₁ ((ω * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = φ₁ ((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := hφ₁Ω ω hω k
    have h2 : ((χ (Matrix.GeneralLinearGroup.det (ω * k)) : ℂˣ) : ℂ) = ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) := by
      rw [map_mul, map_mul, hχΩ ω hω, one_mul]
    have h3 : ((modulus ((Matrix.GeneralLinearGroup.det (ω * k) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) = ((modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) := by
      have h31 := modulus_det_eq_one_of_mem p Ω hΩc ω hω
      rw [map_mul, Units.val_mul, LanglandsTunnell.TateLocal.modulus_mul, NNReal.coe_mul, h31, one_mul]
    rw [kB_apply, h1, h2, h3, ← mul_assoc g ω k]
    ring

  have hconst : ∀ ω : GL (Fin 2) (p.adicCompletion ℚ), ∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g (ω * k) ∂ν = ∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂ν :=
    fun ω => integral_mul_left_eq_self (fun k : GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s g k) ω
  have step3 : ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂ν =
      ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), (∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g (ω * k) ∂ν) ∂ν := by
    rw [show (fun ω : GL (Fin 2) (p.adicCompletion ℚ) => ∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g (ω * k) ∂ν) = fun _ => ∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂ν
      from funext hconst, setIntegral_const, Complex.real_smul]
    rfl

  haveI : IsFiniteMeasure (ν.restrict (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))) := isFiniteMeasure_restrict.mpr hΩfin.ne
  have hprod : Integrable (Function.uncurry fun (ω k : GL (Fin 2) (p.adicCompletion ℚ)) => kB p χ φ₁ φ₂ W₁ w s g (ω * k)) ((ν.restrict (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).prod ν) := by
    refine (integrable_prod_iff ?_).mpr ⟨ae_of_all _ (fun ω => hBg.comp_mul_left ω), ?_⟩
    · exact (hBm.comp (measurable_fst.mul measurable_snd)).aestronglyMeasurable
    · have : (fun ω : GL (Fin 2) (p.adicCompletion ℚ) => ∫ k : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s g (ω * k)‖ ∂ν) = fun _ => ∫ k : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s g k‖ ∂ν :=
        funext fun ω => integral_mul_left_eq_self (fun k : GL (Fin 2) (p.adicCompletion ℚ) => ‖kB p χ φ₁ φ₂ W₁ w s g k‖) ω
      have hI : Integrable (fun ω : GL (Fin 2) (p.adicCompletion ℚ) => ∫ k : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s g (ω * k)‖ ∂ν) (ν.restrict (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))) := by
        rw [this]; exact integrable_const _
      exact hI
  have step4 : ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), (∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g (ω * k) ∂ν) ∂ν =
      ∫ k : GL (Fin 2) (p.adicCompletion ℚ), (∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), kB p χ φ₁ φ₂ W₁ w s g (ω * k) ∂ν) ∂ν :=
    integral_integral_swap (f := fun (ω k : GL (Fin 2) (p.adicCompletion ℚ)) => kB p χ φ₁ φ₂ W₁ w s g (ω * k)) hprod

  have step5 : ∀ k : GL (Fin 2) (p.adicCompletion ℚ), ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), kB p χ φ₁ φ₂ W₁ w s g (ω * k) ∂ν =
      (φ₁ ((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) * (W₁ g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s) * (((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, c j k * wj j g) := by
    intro k
    rw [setIntegral_congr_fun hΩm (fun ω hω => hinv ω hω k), integral_const_mul, hsep g k]

  have step6 : ∫ k : GL (Fin 2) (p.adicCompletion ℚ), (∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), kB p χ φ₁ φ₂ W₁ w s g (ω * k) ∂ν) ∂ν =
      ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, ((W₁ g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s) * wj j g) * (∫ h : GL (Fin 2) (p.adicCompletion ℚ), c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν) := by
    rw [show (fun k : GL (Fin 2) (p.adicCompletion ℚ) => ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), kB p χ φ₁ φ₂ W₁ w s g (ω * k) ∂ν) =
        fun k : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ((W₁ g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s) * wj j g)) *
          (c j k * φ₁ (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) from ?_]
    · rw [integral_finsetSum Finset.univ (fun j _ => (hH3 j).const_mul _), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [integral_const_mul]; ring)
    · funext k
      rw [step5 k, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

  have hall : ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂ν =
      ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, ((W₁ g * (wj j g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) * (∫ h : GL (Fin 2) (p.adicCompletion ℚ), c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν) := by
    rw [step3, step4, step6, add_sub_cancel_right]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  exact mul_left_cancel₀ hΩreal hall

theorem measurable_kB [SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))] (hφ₁ : IsLocallyConstant φ₁) (hφ₂ : IsLocallyConstant φ₂)
    (hW₁ : IsLocallyConstant W₁) (hw : IsLocallyConstant w) (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hχΩ : ∀ ω ∈ Ω, χ (Matrix.GeneralLinearGroup.det ω) = 1) :
    (Measurable fun z : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s z.1 z.2) ∧
    (∀ x : GL (Fin 2) (p.adicCompletion ℚ), Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s g x) ∧
    (Measurable fun z : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s (z.1 * z.2) (z.2⁻¹)) := by
  have hφ₁m : Measurable fun m : GL (Fin 2) (p.adicCompletion ℚ) => φ₁ (m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    (hφ₁.continuous.comp Units.continuous_val).measurable
  have hχm : Measurable fun h : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) :=
    (isLocallyConstant_chi_det p χ Ω hΩo hχΩ).continuous.measurable
  have hdm : Measurable fun h : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp (continuous_modulusR_det p)).measurable
  have hwm : Measurable w := hw.continuous.measurable
  have hW₁m : Measurable W₁ := hW₁.continuous.measurable
  have hE2m : Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) => φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) :=
    (hφ₂.continuous.comp ((Units.continuous_val.matrix_elem 1 0).prodMk (Units.continuous_val.matrix_elem 1 1))).measurable

  have key : ∀ {Z : Type} [MeasurableSpace Z] (a b : Z → GL (Fin 2) (p.adicCompletion ℚ)), Measurable a → Measurable b →
      Measurable fun z : Z => kB p χ φ₁ φ₂ W₁ w s (a z) (b z) := by
    intro Z _ a b ha hb
    simp only [kB_apply]
    exact (((hφ₁m.comp hb).mul (hχm.comp hb)).mul ((hdm.comp hb).pow_const _)).mul
      ((((hW₁m.comp ha).mul (hwm.comp (ha.mul hb))).mul (hE2m.comp ha)).mul ((hdm.comp ha).pow_const _))
  exact ⟨key _ _ measurable_fst measurable_snd, fun x => key _ _ measurable_id measurable_const,
    key _ _ (measurable_fst.mul measurable_snd) measurable_snd.inv⟩

theorem kB_unipotent_mul
    (hW₁law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), W₁ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p (-x) * W₁ g)
    (hwlaw : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) :
    ∀ n ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, ∀ g h : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (n * g) h = kB p χ φ₁ φ₂ W₁ w s g h := by
  rintro n ⟨y, rfl⟩ g h
  have hn : (unipotentGL2Hom (R := (p.adicCompletion ℚ)) y : GL (Fin 2) (p.adicCompletion ℚ)) = unipotent (Multiplicative.toAdd y) :=
    (unipotent_eq_unipotentGL2 p _).symm
  simp only [kB_apply]
  rw [hn, hW₁law, show unipotent (Multiplicative.toAdd y) * g * h = unipotent (Multiplicative.toAdd y) * (g * h) from
    mul_assoc _ _ _, hwlaw]
  have e1 : ∀ j : Fin 2, ((unipotent (Multiplicative.toAdd y) * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j =
      (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j := fun j => by
    rw [unipotent_eq_unipotentGL2]; exact unipotentGL2_mul_apply_one p _ g j
  have e2 : Matrix.GeneralLinearGroup.det (unipotent (Multiplicative.toAdd y) * g : GL (Fin 2) (p.adicCompletion ℚ)) =
      Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, unipotent_eq_unipotentGL2, det_unipotentGL2, one_mul]
  rw [e1 0, e1 1, e2]
  have e3 : NumberField.StandardAddChar.psiLocal ℚ p (-(Multiplicative.toAdd y)) *
      NumberField.StandardAddChar.psiLocal ℚ p (Multiplicative.toAdd y) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (φ₁ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) *
    (W₁ g * w (g * h) * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s)) * e3

theorem integral_kB_mul_right [SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))] [LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ))]
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] [μ₂.IsMulRightInvariant]
    (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure] [μN₂.IsMulRightInvariant]
    (hNcl : IsClosed ((unipotentGL2Hom (R := (p.adicCompletion ℚ))).range : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hsec : ∀ x : GL (Fin 2) (p.adicCompletion ℚ), Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s g x)
    (hNinv : ∀ n ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, ∀ g h : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (n * g) h = kB p χ φ₁ φ₂ W₁ w s g h)
    (k x : GL (Fin 2) (p.adicCompletion ℚ)) :
    ∫ g : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (g * k) x ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) = ∫ g : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g x ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := by
  haveI : LocallyCompactSpace ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := hNcl.locallyCompactSpace
  haveI : SecondCountableTopology ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hWF : ∀ n ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, ∀ g g' : GL (Fin 2) (p.adicCompletion ℚ), (fun _ : GL (Fin 2) (p.adicCompletion ℚ) => (1 : ℂ)) (n * g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s g x) (n * g') =
      (fun _ : GL (Fin 2) (p.adicCompletion ℚ) => (1 : ℂ)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s g x) g' := by
    intro n hn g g'
    show (1 : ℂ) * kB p χ φ₁ φ₂ W₁ w s (n * g') x = 1 * kB p χ φ₁ φ₂ W₁ w s g' x
    rw [hNinv n hn]
  have h44 := (RSCarrier.rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq μ₂
    (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range hNcl μN₂ k (map_mul_right_eq_self μ₂ k) (fun _ => (1 : ℝ)) measurable_const
    (fun _ => one_pos) (fun _ _ => (one_mul (1 : ℝ)).symm) (fun _ _ _ => rfl) (1 / 2) (fun _ => (1 : ℂ))
    (fun g => kB p χ φ₁ φ₂ W₁ w s g x) measurable_const (hsec x) hWF).2
  simpa only [RSCarrier.rsLocalIntegral, one_mul, Complex.ofReal_one, Complex.one_cpow, mul_one] using h44

theorem lintegral_kB_mul_right [SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))] [LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ))]
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] [μ₂.IsMulRightInvariant]
    (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure] [μN₂.IsMulRightInvariant]
    (hNcl : IsClosed ((unipotentGL2Hom (R := (p.adicCompletion ℚ))).range : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hsec : ∀ x : GL (Fin 2) (p.adicCompletion ℚ), Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s g x)
    (hNinv : ∀ n ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, ∀ g h : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (n * g) h = kB p χ φ₁ φ₂ W₁ w s g h)
    (k x : GL (Fin 2) (p.adicCompletion ℚ)) :
    ∫⁻ g : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s (g * k) x‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) = ∫⁻ g : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s g x‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := by
  haveI : LocallyCompactSpace ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := hNcl.locallyCompactSpace
  haveI : SecondCountableTopology ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hD : Measurable (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂) := measurable_density' _ μN₂
  have hf : Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) => ‖kB p χ φ₁ φ₂ W₁ w s g x‖ₑ := (hsec x).enorm
  have hfk : Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) => ‖kB p χ φ₁ φ₂ W₁ w s (g * k) x‖ₑ := hf.comp (measurable_mul_const k)
  rw [lintegral_withDensity_eq_lintegral_mul _ hD hfk, lintegral_withDensity_eq_lintegral_mul _ hD hf]
  exact HaarQuotient.lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range hNcl μN₂
    (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ‖kB p χ φ₁ φ₂ W₁ w s g x‖ₑ) hf (fun n hn g => by simp only [hNinv n hn]) k (map_mul_right_eq_self μ₂ k)

theorem integrable_shear [SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))] [LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ))]
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] [μ₂.IsMulRightInvariant]
    (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure] [μN₂.IsMulRightInvariant]
    (hNcl : IsClosed ((unipotentGL2Hom (R := (p.adicCompletion ℚ))).range : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (hKm : Measurable fun z : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s z.1 z.2)
    (hsec : ∀ x : GL (Fin 2) (p.adicCompletion ℚ), Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s g x)
    (hAm : Measurable fun z : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) => kB p χ φ₁ φ₂ W₁ w s (z.1 * z.2) (z.2⁻¹))
    (hNinv : ∀ n ∈ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range, ∀ g h : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (n * g) h = kB p χ φ₁ φ₂ W₁ w s g h)
    (hH1 : Integrable (Function.uncurry (kB p χ φ₁ φ₂ W₁ w s)) ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν)) :
    Integrable (Function.uncurry fun (g k : GL (Fin 2) (p.adicCompletion ℚ)) => kB p χ φ₁ φ₂ W₁ w s (g * k) (k⁻¹)) ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν) := by
  haveI : LocallyCompactSpace ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := hNcl.locallyCompactSpace
  haveI : SecondCountableTopology ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range := sigmaCompactSpace_of_locallyCompact_secondCountable
  refine ⟨hAm.aestronglyMeasurable, ?_⟩
  have hfin := hH1.2
  rw [hasFiniteIntegral_iff_enorm] at hfin ⊢
  have hRIl := lintegral_kB_mul_right p χ φ₁ φ₂ W₁ w s μ₂ μN₂ hNcl hsec hNinv
  calc ∫⁻ z, ‖Function.uncurry (fun (g k : GL (Fin 2) (p.adicCompletion ℚ)) => kB p χ φ₁ φ₂ W₁ w s (g * k) (k⁻¹)) z‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν
      = ∫⁻ g : GL (Fin 2) (p.adicCompletion ℚ), ∫⁻ k : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s (g * k) (k⁻¹)‖ₑ ∂ν ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) :=
        lintegral_prod _ hAm.enorm.aemeasurable
    _ = ∫⁻ k : GL (Fin 2) (p.adicCompletion ℚ), ∫⁻ g : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s (g * k) (k⁻¹)‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∂ν :=
        lintegral_lintegral_swap hAm.enorm.aemeasurable
    _ = ∫⁻ k : GL (Fin 2) (p.adicCompletion ℚ), ∫⁻ g : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s g (k⁻¹)‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∂ν := by
        simp only [hRIl]
    _ = ∫⁻ k : GL (Fin 2) (p.adicCompletion ℚ), ∫⁻ g : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s g k‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∂ν :=
        lintegral_inv_eq_self (fun k : GL (Fin 2) (p.adicCompletion ℚ) => ∫⁻ g : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s g k‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)))
    _ = ∫⁻ g : GL (Fin 2) (p.adicCompletion ℚ), ∫⁻ k : GL (Fin 2) (p.adicCompletion ℚ), ‖kB p χ φ₁ φ₂ W₁ w s g k‖ₑ ∂ν ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) :=
        (lintegral_lintegral_swap hKm.enorm.aemeasurable).symm
    _ = ∫⁻ z, ‖Function.uncurry (kB p χ φ₁ φ₂ W₁ w s) z‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν :=
        (lintegral_prod _ hKm.enorm.aemeasurable).symm
    _ < ⊤ := hfin

theorem S2_shear [SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))] [LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ))]
    (hφ₁ : IsLocallyConstant φ₁) (hφ₂ : IsLocallyConstant φ₂) (hW₁ : IsLocallyConstant W₁) (hw : IsLocallyConstant w)
    (hW₁law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), W₁ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p (-x) * W₁ g)
    (hwlaw : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hχΩ : ∀ ω ∈ Ω, χ (Matrix.GeneralLinearGroup.det ω) = 1)
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] [μ₂.IsMulRightInvariant]
    (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure] [μN₂.IsMulRightInvariant]
    (hNcl : IsClosed ((unipotentGL2Hom (R := (p.adicCompletion ℚ))).range : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [ν.IsInvInvariant]
    (hH1 : Integrable (Function.uncurry (kB p χ φ₁ φ₂ W₁ w s )) ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν)) :
    ∫ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (g * k) (k⁻¹) ∂ν) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) =
      ∫ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂ν) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := by
  obtain ⟨hKm, hsec, hAm⟩ := measurable_kB p χ φ₁ φ₂ W₁ w s hφ₁ hφ₂ hW₁ hw Ω hΩo hχΩ
  have hNinv := kB_unipotent_mul p χ φ₁ φ₂ W₁ w s hW₁law hwlaw
  have hRI := integral_kB_mul_right p χ φ₁ φ₂ W₁ w s μ₂ μN₂ hNcl hsec hNinv
  have hAint := integrable_shear p χ φ₁ φ₂ W₁ w s μ₂ μN₂ hNcl ν hKm hsec hAm hNinv hH1
  calc ∫ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (g * k) (k⁻¹) ∂ν) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))
      = ∫ k : GL (Fin 2) (p.adicCompletion ℚ), (∫ g : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (g * k) (k⁻¹) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) ∂ν :=
        integral_integral_swap hAint
    _ = ∫ k : GL (Fin 2) (p.adicCompletion ℚ), (∫ g : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g (k⁻¹) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) ∂ν := by simp only [hRI]
    _ = ∫ k : GL (Fin 2) (p.adicCompletion ℚ), (∫ g : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) ∂ν :=
        integral_inv_eq_self (fun k : GL (Fin 2) (p.adicCompletion ℚ) => ∫ g : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) ν
    _ = ∫ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂ν) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) :=
        (integral_integral_swap hH1).symm

end Steps

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem main

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)

    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂)
    (W₁ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hW₁ : IsLocallyConstant W₁)
    (hW₁law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W₁ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p (-x) * W₁ g)

    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : IsLocallyConstant w)
    (hwlaw : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)

    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))) (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hφ₁Ω : ∀ ω ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      φ₁ ((ω * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = φ₁ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
    (hχΩ : ∀ ω ∈ Ω, χ (Matrix.GeneralLinearGroup.det ω) = 1)

    (ι : Type) [Fintype ι]
    (wj : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hwj : ∀ j, IsLocallyConstant (wj j))
    (c : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hc : ∀ j, IsLocallyConstant (c j)) :
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure]
      (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure],
    (∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g * ω * h) ∂ν =
          ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, c j h * wj j g) →
    ∀ s : ℂ,

      Integrable (fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
            (W₁ gh.1 * w (gh.1 * gh.2) *
              φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))
        ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν) →

      (∀ j, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (W₁ g * (wj j g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) →

      (∀ j, Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) ν) →

      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
              ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
                φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  φ₂ (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  W₁ h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν)
          w =
        ∑ j, RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          (s + 1 / 2)
          W₁
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => wj j g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
            ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
              c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν := by
  intro μ₂ _hμ₂ μN₂ _hμN₂ ν _hν hsep s hH1 hH2 hH3
  obtain ⟨hsc, hlc, hNcl, hNright⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hsc
  haveI := hlc
  haveI : μN₂.IsMulRightInvariant := hNright μN₂
  obtain ⟨hνR, hνI⟩ := Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two ν
  haveI := hνR
  haveI := hνI
  obtain ⟨hμR, -⟩ := Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ₂
  haveI := hμR
  have hH1' : Integrable (Function.uncurry (kB p χ φ₁ φ₂ W₁ w s)) ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν) := hH1
  have S1 := S1_pointwise p χ φ₁ φ₂ W₁ w s ν
  have S2 := S2_shear p χ φ₁ φ₂ W₁ w s hφ₁ hφ₂ hW₁ hw hW₁law hwlaw Ω hΩo hχΩ μ₂ μN₂ hNcl ν hH1'
  have S3ae : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s g k ∂ν) =ᵐ[(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))]
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, ((W₁ g * (wj j g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) * (∫ h : GL (Fin 2) (p.adicCompletion ℚ), c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν)) := by
    filter_upwards [hH1'.prod_right_ae] with g hg
    exact S3_average p χ φ₁ φ₂ W₁ w s hφ₁ hw Ω hΩo hΩc hφ₁Ω hχΩ wj c ν hsep hH3 g hg
  have S4 :
      ∫ g : GL (Fin 2) (p.adicCompletion ℚ), (∑ j, ((W₁ g * (wj j g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) * (∫ h : GL (Fin 2) (p.adicCompletion ℚ), c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν)) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) =
        ∑ j, (∫ g : GL (Fin 2) (p.adicCompletion ℚ), ((W₁ g * (wj j g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) * (∫ h : GL (Fin 2) (p.adicCompletion ℚ), c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν) := by
    rw [integral_finsetSum Finset.univ (fun j _ => (hH2 j).mul_const _)]
    exact Finset.sum_congr rfl (fun j _ => integral_mul_const _ _)
  have L : ∫ g : GL (Fin 2) (p.adicCompletion ℚ), ((((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
              ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
                φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  φ₂ (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  W₁ h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν) * w g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) =
      ∑ j, (∫ g : GL (Fin 2) (p.adicCompletion ℚ), ((W₁ g * (wj j g * φ₂ (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) * (∫ h : GL (Fin 2) (p.adicCompletion ℚ), c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν) :=
    calc _ = ∫ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ k : GL (Fin 2) (p.adicCompletion ℚ), kB p χ φ₁ φ₂ W₁ w s (g * k) (k⁻¹) ∂ν) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) :=
          integral_congr_ae (ae_of_all _ S1)
      _ = _ := S2
      _ = _ := integral_congr_ae S3ae
      _ = _ := S4
  exact L

end Main

end LanglandsTunnell.RankinSelberg.UnfoldGodement32

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)

    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂)
    (W₁ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hW₁ : IsLocallyConstant W₁)
    (hW₁law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W₁ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p (-x) * W₁ g)

    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : IsLocallyConstant w)
    (hwlaw : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)

    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))) (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hφ₁Ω : ∀ ω ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      φ₁ ((ω * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = φ₁ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
    (hχΩ : ∀ ω ∈ Ω, χ (Matrix.GeneralLinearGroup.det ω) = 1)

    (ι : Type) [Fintype ι]
    (wj : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hwj : ∀ j, IsLocallyConstant (wj j))
    (c : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hc : ∀ j, IsLocallyConstant (c j)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure]
      (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure],
    (∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g * ω * h) ∂ν =
          ((ν (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, c j h * wj j g) →
    ∀ s : ℂ,

      Integrable (fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
            (W₁ gh.1 * w (gh.1 * gh.2) *
              φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))
        ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν) →

      (∀ j, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (W₁ g * (wj j g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1))) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) →

      (∀ j, Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) ν) →

      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          s
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
              ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
                φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  φ₂ (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  W₁ h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν)
          w =
        ∑ j, RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
          (s + 1 / 2)
          W₁
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => wj j g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
            ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
              c j h * φ₁ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2) ∂ν :=
  LanglandsTunnell.RankinSelberg.UnfoldGodement32.main p χ φ₁ hφ₁ φ₂ hφ₂ W₁ hW₁ hW₁law w hw hwlaw Ω hΩo hΩc hφ₁Ω hχΩ
    ι wj hwj c hc

end S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_godementWhittaker_iotaGL_eq_sum_rsLocalIntegral_mul_godementZeta (solution)
