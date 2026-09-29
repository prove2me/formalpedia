-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f74622fb-1f3a-5b25-9c2a-b2335cc3e055

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_iotaGL_jacquetIntegral_eq_mul_integral_localZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta31_fe_of_forall_localZeta31_fe
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnits2_mul_longWeyl3_upperUnipotent3_weylPrime3_eq_central_mul_of_isGL3PsiWhittakerFn
import Theorems.Thm_MvPolynomial_exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torusShellAverage_mul_eval_eq_and_dual_of_admissible_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetIntegral_spherical_laws_of_unramified_of_norm_lt
import Theorems.Thm_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasSum_shell_localZeta30_one_iotaGL_scalarPi_zpow_of_iotaGL_invariant
import Theorems.Thm_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left
import Theorems.Thm_LanglandsTunnell_TateLocal_addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat
import Theorems.Thm_LanglandsTunnell_CubicInduction_dualSection_mem_principalSeries2_and_jacquetIntegral_eq
import Theorems.Thm_Complex_forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_localZeta31_fe_of_twist_modulus_cpow
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central
import Theorems.Thm_LanglandsTunnell_CubicInduction_ne_zero_and_ne_zero_of_forall_localZeta30_eq_inv_eval_mul_and_localZetaDual31_eq_inv_eval_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant
p2m_attr_erase "simp" "AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 UnramifiedWhittaker LanglandsTunnell.TateLocal NumberField.TateGlobal"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"
open scoped Topology ENNReal NNReal Matrix

namespace Ws1
namespace Middle
namespace DualKit

noncomputable section

section Algebra

variable {A : Type*} [CommRing A]

theorem transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  rw [transposeInv3_coe]
  have : ((transposeInv3 g)⁻¹ : GL (Fin 3) A) = transposeInv3 g⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← transposeInv3_mul, mul_inv_cancel]
    refine Units.ext ?_
    rw [transposeInv3_coe, inv_one, Units.val_one, Matrix.transpose_one]
  rw [this, transposeInv3_coe, inv_inv, Matrix.transpose_transpose]

theorem embedMat2_transpose (M : Matrix (Fin 2) (Fin 2) A) : embedMat2 Mᵀ = (embedMat2 M)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem transposeInv3_iotaGL (h : GL (Fin 2) A) :
    transposeInv3 (iotaGL h) = iotaGL (transposeInvN (Fin 2) h) := by
  refine Units.ext ?_
  rw [transposeInv3_coe, ← map_inv, coe_iotaGL, coe_iotaGL, coe_transposeInvN, embedMat2_transpose]

end Algebra

section DualLaw

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem coe_transposeInv3_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    ((transposeInv3 (upperUnipotent3 x y z) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
  have hinv : (((upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  change (((upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ = _
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem longWeyl3_mul_self : (longWeyl3 : LocalGL3 v) * longWeyl3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem longWeyl3_inv : (longWeyl3 : LocalGL3 v)⁻¹ = longWeyl3 :=
  inv_eq_of_mul_eq_one_right longWeyl3_mul_self

theorem weylPrime3_mul_self : (weylPrime3 : LocalGL3 v) * weylPrime3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3 (x y z : v.adicCompletion ℚ) :
    (longWeyl3 : LocalGL3 v) * transposeInv3 (upperUnipotent3 x y z) * longWeyl3 =
      upperUnipotent3 (-y) (-x) (x * y - z) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeInv3_upperUnipotent3, longWeyl3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem isGL3PsiWhittakerFn_inv_dualWhittakerFn3 {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) : IsGL3PsiWhittakerFn ψ⁻¹ (dualWhittakerFn3 W) := by
  intro x y z g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul]
  have h : (longWeyl3 : LocalGL3 v) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
      upperUnipotent3 (-y) (-x) (x * y - z) * (longWeyl3 * transposeInv3 g) := by
    rw [← longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3]
    have : (longWeyl3 : LocalGL3 v) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
        longWeyl3 * transposeInv3 (upperUnipotent3 x y z) * longWeyl3⁻¹ * (longWeyl3 * transposeInv3 g) := by
      group
    rw [this, longWeyl3_inv]
  rw [h, hW, AddChar.inv_apply]
  congr 2
  ring

theorem isGL3PsiWhittakerFn_rightTranslate {ψ : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (h : LocalGL3 v) : IsGL3PsiWhittakerFn ψ (fun x => W (x * h)) := by
  intro x y z g
  show W (upperUnipotent3 x y z * g * h) = ψ (x + y) * W (g * h)
  rw [mul_assoc]
  exact hW x y z (g * h)

end DualLaw

section DualSmooth

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem continuous_transposeInv3 : Continuous (transposeInv3 : LocalGL3 v → LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun g : LocalGL3 v => (((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : LocalGL3 v => ((g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ
    exact Units.continuous_val.matrix_transpose

def tau3 (v : HeightOneSpectrum (𝓞 ℚ)) : LocalGL3 v →* LocalGL3 v where
  toFun := transposeInv3
  map_one' := by
    refine Units.ext ?_
    rw [transposeInv3_coe, inv_one, Units.val_one, Matrix.transpose_one]
  map_mul' := transposeInv3_mul

theorem smooth_dualWhittakerFn3 {W : LocalGL3 v → ℂ}
    (hWsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, dualWhittakerFn3 W (g * k) = dualWhittakerFn3 W g := by
  obtain ⟨Uv, hUv, hinv⟩ := hWsm
  refine ⟨Uv.comap (tau3 v), hUv.preimage continuous_transposeInv3, fun k hk g => ?_⟩
  change W (longWeyl3 * transposeInv3 (g * k)) = W (longWeyl3 * transposeInv3 g)
  rw [transposeInv3_mul, ← mul_assoc]
  exact hinv (transposeInv3 k) hk _

theorem smooth_rightTranslate {W : LocalGL3 v → ℂ}
    (hWsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (h : LocalGL3 v) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, (fun x => W (x * h)) (g * k) = (fun x => W (x * h)) g := by
  obtain ⟨Uv, hUv, hinv⟩ := hWsm
  let φ : LocalGL3 v →* LocalGL3 v := (MulAut.conj h⁻¹).toMonoidHom
  refine ⟨Uv.comap φ, ?_, ?_⟩
  · have hφ : Continuous φ := by
      change Continuous fun x : LocalGL3 v => h⁻¹ * x * h⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const
    exact hUv.preimage hφ
  · intro k hk g
    have hk' : h⁻¹ * k * h ∈ Uv := by
      have := hk
      rw [Subgroup.mem_comap] at this
      simpa [φ] using this
    show W (g * k * h) = W (g * h)
    have : g * k * h = g * h * (h⁻¹ * k * h) := by group
    rw [this, hinv _ hk']

theorem smooth_of_mem_gl3CyclicSubspace {W₃ : LocalGL3 v → ℂ}
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W₃ (g * k) = W₃ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g := by
  refine Submodule.span_induction (p := fun W _ =>
      ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
      ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩
    obtain ⟨Uv, hUv, hinv⟩ := smooth_rightTranslate hW₃sm h
    exact ⟨Uv, hUv, fun k hk g => by simpa only [gl3AmbientRightTranslate_apply] using hinv k hk g⟩
  · obtain ⟨Uv, hUv, _⟩ := hW₃sm
    exact ⟨Uv, hUv, fun k _ g => rfl⟩
  · rintro f g _ _ ⟨U₁, hU₁, h₁⟩ ⟨U₂, hU₂, h₂⟩
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk x => ?_⟩
    · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
    · simp only [Pi.add_apply]
      rw [h₁ k (Subgroup.mem_inf.mp hk).1, h₂ k (Subgroup.mem_inf.mp hk).2]
  · rintro a f _ ⟨U, hU, h⟩
    exact ⟨U, hU, fun k hk x => by simp only [Pi.smul_apply, smul_eq_mul]; rw [h k hk]⟩

theorem law_of_mem_gl3CyclicSubspace {θ : AddChar (v.adicCompletion ℚ) ℂ} {W₃ : LocalGL3 v → ℂ}
    (hW₃law : IsGL3PsiWhittakerFn θ W₃) {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    IsGL3PsiWhittakerFn θ W := by
  have hle : gl3CyclicSubspace W₃ ≤ gl3PsiWhittakerFnSpace (v.adicCompletion ℚ) ℂ θ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace θ h ((mem_gl3PsiWhittakerFnSpace_iff θ _).mpr hW₃law)
  exact (mem_gl3PsiWhittakerFnSpace_iff θ _).mp (hle hW)

end DualSmooth

section Haar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

scoped instance borelSpace_units_adic : BorelSpace (v.adicCompletion ℚ)ˣ := borelSpace_units

scoped instance isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

scoped instance isHaarMeasure_mulHaar :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure (v.adicCompletion ℚ)ˣ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure ℚ v (selfDualHaarAt ℚ v)

end Haar

end

end Ws1.Middle.DualKit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp AutomorphicForm~lowerUnipotentGL2"

namespace Ws1
namespace MiddleKit2

variable {K : Type*} [Field K]

theorem weylPrime3_mul_iotaGL_weyl (w₀ : GL (Fin 2) K) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0]) :
    (weylPrime3 : GL (Fin 3) K) * iotaGL w₀ = longWeyl3 * weylPrime3 := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, hw₀]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, longWeyl3, weylPrime3, Matrix.mul_apply, Fin.sum_univ_three]

theorem weylPrime3_mul_iotaGL_diagUnits2 (α β : Kˣ) :
    (weylPrime3 : GL (Fin 3) K) * iotaGL (diagUnits2 α β) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) β * iotaGL (diagUnits2 (α * β⁻¹) β⁻¹) * weylPrime3 := by
  apply Units.ext
  have h2 : (β : K) ≠ 0 := β.ne_zero
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnits2, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, weylPrime3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.GeneralLinearGroup.scalar, h2]
  field_simp

theorem lowerUnipotent21_eq_iotaGL_bruhat (u : Kˣ) (w₀ : GL (Fin 2) K)
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0]) :
    (lowerUnipotent21 (u : K) : GL (Fin 3) K) =
      iotaGL (unipotentGL2 ((u : K)⁻¹) * diagUnits2 (-u⁻¹) u * w₀ * unipotentGL2 ((u : K)⁻¹)) := by
  apply Units.ext
  have hu : (u : K) ≠ 0 := u.ne_zero
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnits2, unipotentGL2_coe, hw₀, Units.val_neg,
    Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, lowerUnipotent21, Matrix.mul_apply, Fin.sum_univ_two, hu]

end Ws1.MiddleKit2
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace Ws1
namespace Middle
namespace TorusUnique

open MvPolynomial

def LRep (f : ℂ → ℂ → ℂ) : Prop :=
  ∃ (M : MvPolynomial (Fin 2) ℂ) (A B : ℕ),
    ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → f x y * x ^ A * y ^ B = MvPolynomial.eval ![x, y] M

namespace LRep

theorem const (c : ℂ) : LRep fun _ _ => c :=
  ⟨MvPolynomial.C c, 0, 0, by intro x y _ _; simp⟩

theorem fst : LRep fun x _ => x :=
  ⟨MvPolynomial.X 0, 0, 0, by intro x y _ _; simp⟩

theorem snd : LRep fun _ y => y :=
  ⟨MvPolynomial.X 1, 0, 0, by intro x y _ _; simp⟩

theorem fst_inv : LRep fun x _ => x⁻¹ :=
  ⟨1, 1, 0, by intro x y hx _; simp [hx]⟩

theorem snd_inv : LRep fun _ y => y⁻¹ :=
  ⟨1, 0, 1, by intro x y _ hy; simp [hy]⟩

theorem add {f g : ℂ → ℂ → ℂ} (hf : LRep f) (hg : LRep g) :
    LRep fun x y => f x y + g x y := by
  obtain ⟨M, A, B, hM⟩ := hf
  obtain ⟨M', A', B', hM'⟩ := hg
  refine ⟨M * (X 0 ^ A' * X 1 ^ B') + M' * (X 0 ^ A * X 1 ^ B), A + A', B + B',
    fun x y hx hy => ?_⟩
  simp only [map_add, map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [← hM x y hx hy, ← hM' x y hx hy]
  ring

theorem mul {f g : ℂ → ℂ → ℂ} (hf : LRep f) (hg : LRep g) :
    LRep fun x y => f x y * g x y := by
  obtain ⟨M, A, B, hM⟩ := hf
  obtain ⟨M', A', B', hM'⟩ := hg
  refine ⟨M * M', A + A', B + B', fun x y hx hy => ?_⟩
  simp only [map_mul]
  rw [← hM x y hx hy, ← hM' x y hx hy]
  ring

theorem neg {f : ℂ → ℂ → ℂ} (hf : LRep f) : LRep fun x y => -f x y := by
  have := (const (-1)).mul hf
  refine (this.elim fun M h => ⟨M, ?_⟩)
  obtain ⟨A, B, h⟩ := h
  exact ⟨A, B, fun x y hx hy => by rw [← h x y hx hy]; ring⟩

theorem sub {f g : ℂ → ℂ → ℂ} (hf : LRep f) (hg : LRep g) :
    LRep fun x y => f x y - g x y := by
  have := hf.add hg.neg
  obtain ⟨M, A, B, h⟩ := this
  exact ⟨M, A, B, fun x y hx hy => by rw [← h x y hx hy]; ring⟩

theorem pow {f : ℂ → ℂ → ℂ} (hf : LRep f) (n : ℕ) : LRep fun x y => f x y ^ n := by
  induction n with
  | zero => simpa using const 1
  | succ n ih =>
    obtain ⟨M, A, B, h⟩ := ih.mul hf
    exact ⟨M, A, B, fun x y hx hy => by rw [← h x y hx hy]; ring⟩

theorem const_mul {f : ℂ → ℂ → ℂ} (c : ℂ) (hf : LRep f) : LRep fun x y => c * f x y :=
  (const c).mul hf

theorem zpow_fst (i : ℤ) : LRep fun x _ => x ^ i := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · obtain ⟨M, A, B, h⟩ := fst.pow n
    exact ⟨M, A, B, fun x y hx hy => by beta_reduce; rw [zpow_natCast]; exact h x y hx hy⟩
  · refine ⟨1, n, 0, fun x y hx _ => ?_⟩
    simp [zpow_neg, zpow_natCast, hx]

theorem zpow_snd (j : ℤ) : LRep fun _ y => y ^ j := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · obtain ⟨M, A, B, h⟩ := snd.pow n
    exact ⟨M, A, B, fun x y hx hy => by beta_reduce; rw [zpow_natCast]; exact h x y hx hy⟩
  · refine ⟨1, 0, n, fun x y _ hy => ?_⟩
    simp [zpow_neg, zpow_natCast, hy]

theorem monomial (a : ℂ) (i j : ℤ) : LRep fun x y => a * x ^ i * y ^ j :=
  ((const a).mul (zpow_fst i)).mul (zpow_snd j)

theorem polynomial_eval {g : ℂ → ℂ → ℂ} (hg : LRep g) (E : Polynomial ℂ) :
    LRep fun x y => E.eval (g x y) := by
  induction E using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact hp.add hq
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    exact (const a).mul (hg.pow n)

theorem polynomial_eval_monomial (E : Polynomial ℂ) (a : ℂ) (i j : ℤ) :
    LRep fun x y => E.eval (a * x ^ i * y ^ j) :=
  (monomial a i j).polynomial_eval E

theorem mvPolynomial_eval {g₁ g₂ : ℂ → ℂ → ℂ} (h₁ : LRep g₁) (h₂ : LRep g₂)
    (P : MvPolynomial (Fin 2) ℂ) :
    LRep fun x y => MvPolynomial.eval ![g₁ x y, g₂ x y] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using const a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    fin_cases i
    · simpa using hp.mul h₁
    · simpa using hp.mul h₂

theorem mvPolynomial_eval_self (P : MvPolynomial (Fin 2) ℂ) :
    LRep fun x y => MvPolynomial.eval ![x, y] P :=
  mvPolynomial_eval fst snd P

theorem mvPolynomial_eval_inv_fst (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    LRep fun x y => MvPolynomial.eval ![c * x⁻¹, y] P :=
  mvPolynomial_eval ((const c).mul fst_inv) snd P

theorem mvPolynomial_eval_monomial (P : MvPolynomial (Fin 2) ℂ) (a b : ℂ) (i j k l : ℤ) :
    LRep fun x y => MvPolynomial.eval ![a * x ^ i * y ^ j, b * x ^ k * y ^ l] P :=
  mvPolynomial_eval (monomial a i j) (monomial b k l) P

end LRep
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

theorem mv_eq_of_forall_mem_forall_mem_eval_eq {K : Type*} [CommRing K] [IsDomain K]
    (P Q : MvPolynomial (Fin 2) K) (S T : Set K) (hS : S.Infinite) (hT : T.Infinite)
    (h : ∀ x ∈ S, ∀ y ∈ T, MvPolynomial.eval ![x, y] P = MvPolynomial.eval ![x, y] Q) :
    P = Q := by
  refine MvPolynomial.funext_set ![S, T] (fun i => by fin_cases i <;> simpa) ?_
  intro v hv
  have h0 : v 0 ∈ S := by simpa using hv 0 (Set.mem_univ _)
  have h1 : v 1 ∈ T := by simpa using hv 1 (Set.mem_univ _)
  have hv' : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv']; exact h _ h0 _ h1

theorem LRep.eq_of_forall_mem {f g : ℂ → ℂ → ℂ} (hf : LRep f) (hg : LRep g) (S T : Set ℂ)
    (hS : S.Infinite) (hT : T.Infinite) (hS0 : ∀ x ∈ S, x ≠ 0) (hT0 : ∀ y ∈ T, y ≠ 0)
    (h : ∀ x ∈ S, ∀ y ∈ T, f x y = g x y) :
    ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → f x y = g x y := by
  obtain ⟨M, A, B, hM⟩ := hf
  obtain ⟨M', A', B', hM'⟩ := hg
  have key : M * (X 0 ^ A' * X 1 ^ B') = M' * (X 0 ^ A * X 1 ^ B) := by
    refine mv_eq_of_forall_mem_forall_mem_eval_eq _ _ S T hS hT fun x hx y hy => ?_
    simp only [map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hM x y (hS0 x hx) (hT0 y hy), ← hM' x y (hS0 x hx) (hT0 y hy), h x hx y hy]
    ring
  intro x y hx hy
  have e := congrArg (MvPolynomial.eval ![x, y]) key
  simp only [map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one] at e
  rw [← hM x y hx hy, ← hM' x y hx hy] at e
  have hxA : x ^ A * x ^ A' ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hx)
  have hyB : y ^ B * y ^ B' ≠ 0 := mul_ne_zero (pow_ne_zero _ hy) (pow_ne_zero _ hy)
  have : f x y * (x ^ A * x ^ A') * (y ^ B * y ^ B') = g x y * (x ^ A * x ^ A') * (y ^ B * y ^ B') := by
    calc f x y * (x ^ A * x ^ A') * (y ^ B * y ^ B') = f x y * x ^ A * y ^ B * (x ^ A' * y ^ B') := by ring
      _ = g x y * x ^ A' * y ^ B' * (x ^ A * y ^ B) := e
      _ = g x y * (x ^ A * x ^ A') * (y ^ B * y ^ B') := by ring
  have h2 : f x y * (x ^ A * x ^ A') = g x y * (x ^ A * x ^ A') := mul_right_cancel₀ hyB this
  exact mul_right_cancel₀ hxA h2

theorem infinite_puncturedBall {ρ : ℝ} (hρ : 0 < ρ) : Set.Infinite {x : ℂ | x ≠ 0 ∧ ‖x‖ < ρ} := by
  have hinj : Function.Injective (fun t : ℝ => (t : ℂ)) := fun a b h => Complex.ofReal_injective h
  refine ((Set.Ioo_infinite hρ).image hinj.injOn).mono ?_
  rintro _ ⟨t, ⟨ht0, htρ⟩, rfl⟩
  refine ⟨Complex.ofReal_ne_zero.2 ht0.ne', ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  exact htρ

theorem tsum_shift (A : ℤ × ℤ → ℂ) (N N' : ℤ) (hle : N ≤ N')
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N' ∨ n.2 < N') → A n = 0) (X Y : ℂ) :
    ∑' m : ℕ × ℕ, A (N + (m.1 : ℤ), N + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2 =
      X ^ (N' - N).toNat * Y ^ (N' - N).toNat *
        ∑' m : ℕ × ℕ, A (N' + (m.1 : ℤ), N' + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2 := by
  set d : ℕ := (N' - N).toNat with hd
  have hdN : N + (d : ℤ) = N' := by rw [hd, Int.toNat_of_nonneg (sub_nonneg.2 hle)]; ring
  have hinj : Function.Injective (fun m : ℕ × ℕ => (m.1 + d, m.2 + d)) := by
    intro a b h
    simp only [Prod.mk.injEq, add_left_inj] at h
    exact Prod.ext h.1 h.2
  rw [← tsum_mul_left, ← hinj.tsum_eq]
  · refine tsum_congr fun m => ?_
    simp only [Nat.cast_add, pow_add]
    rw [show N + ((m.1 : ℤ) + (d : ℤ)) = N' + (m.1 : ℤ) by rw [← hdN]; ring,
      show N + ((m.2 : ℤ) + (d : ℤ)) = N' + (m.2 : ℤ) by rw [← hdN]; ring]
    ring
  · intro m hm
    rw [Function.mem_support] at hm
    have h1 : N' ≤ N + (m.1 : ℤ) := by
      by_contra h; exact hm (by rw [hsupp _ (Or.inl (not_le.1 h)), zero_mul, zero_mul])
    have h2 : N' ≤ N + (m.2 : ℤ) := by
      by_contra h; exact hm (by rw [hsupp _ (Or.inr (not_le.1 h)), zero_mul, zero_mul])
    refine ⟨(m.1 - d, m.2 - d), ?_⟩
    have : (d : ℤ) ≤ m.1 := by linarith
    have : (d : ℤ) ≤ m.2 := by linarith
    ext <;> simp <;> omega

variable (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
  (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (Φ : LocalGL3 v → ℂ)

theorem torus_cleared_eq_of_le_of_small
    (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ)
    (N₁' : ℤ) (D₁' D₂' : Polynomial ℂ) (P' : MvPolynomial (Fin 2) ℂ) (r' : ℝ) (hle : N₁ ≤ N₁')
    (h : ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      (∑' m : ℕ × ℕ, Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (m.2 : ℤ)) *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (m.1 : ℤ))))) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
        MvPolynomial.eval ![X, Y] P)
    (hsupp' : ∀ n : ℤ × ℤ, (n.1 < N₁' ∨ n.2 < N₁') → Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1))) = 0)
    (h' : ∀ X Y : ℂ, ‖X‖ < r' → ‖Y‖ < r' →
      (∑' m : ℕ × ℕ, Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.2 : ℤ)) *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.1 : ℤ))))) * X ^ m.1 * Y ^ m.2) * (D₁'.eval X * D₂'.eval Y) =
        MvPolynomial.eval ![X, Y] P')
    (X Y : ℂ) (hX0 : X ≠ 0) (hY0 : Y ≠ 0) (hX : ‖X‖ < r) (hY : ‖Y‖ < r) (hX' : ‖X‖ < r') (hY' : ‖Y‖ < r') :
    X ^ N₁ * Y ^ N₁ * MvPolynomial.eval ![X, Y] P * (D₁'.eval X * D₂'.eval Y) =
      X ^ N₁' * Y ^ N₁' * MvPolynomial.eval ![X, Y] P' * (D₁.eval X * D₂.eval Y) := by
  have hs := tsum_shift (fun n : ℤ × ℤ => Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))) N₁ N₁' hle hsupp' X Y
  simp only [] at hs
  have hd : ((N₁' - N₁).toNat : ℤ) = N₁' - N₁ := Int.toNat_of_nonneg (sub_nonneg.2 hle)
  have hXp : X ^ N₁ * X ^ (N₁' - N₁).toNat = X ^ N₁' := by
    rw [← zpow_natCast, ← zpow_add₀ hX0, hd]; ring_nf
  have hYp : Y ^ N₁ * Y ^ (N₁' - N₁).toNat = Y ^ N₁' := by
    rw [← zpow_natCast, ← zpow_add₀ hY0, hd]; ring_nf
  rw [← h X Y hX hY, ← h' X Y hX' hY', hs]
  calc X ^ N₁ * Y ^ N₁ *
        (X ^ (N₁' - N₁).toNat * Y ^ (N₁' - N₁).toNat *
            (∑' m : ℕ × ℕ, Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.2 : ℤ)) *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.1 : ℤ))))) * X ^ m.1 * Y ^ m.2) *
          (D₁.eval X * D₂.eval Y)) * (D₁'.eval X * D₂'.eval Y)
      = (X ^ N₁ * X ^ (N₁' - N₁).toNat) * (Y ^ N₁ * Y ^ (N₁' - N₁).toNat) *
          ((∑' m : ℕ × ℕ, Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.2 : ℤ)) *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.1 : ℤ))))) * X ^ m.1 * Y ^ m.2) *
            (D₁'.eval X * D₂'.eval Y)) * (D₁.eval X * D₂.eval Y) := by ring
    _ = X ^ N₁' * Y ^ N₁' *
          ((∑' m : ℕ × ℕ, Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.2 : ℤ)) *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.1 : ℤ))))) * X ^ m.1 * Y ^ m.2) *
            (D₁'.eval X * D₂'.eval Y)) * (D₁.eval X * D₂.eval Y) := by rw [hXp, hYp]

theorem torus_cleared_eq
    (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1))) = 0)
    (h : ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      (∑' m : ℕ × ℕ, Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (m.2 : ℤ)) *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (m.1 : ℤ))))) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
        MvPolynomial.eval ![X, Y] P)
    (N₁' : ℤ) (D₁' D₂' : Polynomial ℂ) (P' : MvPolynomial (Fin 2) ℂ) (r' : ℝ) (hr' : 0 < r')
    (hsupp' : ∀ n : ℤ × ℤ, (n.1 < N₁' ∨ n.2 < N₁') → Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1))) = 0)
    (h' : ∀ X Y : ℂ, ‖X‖ < r' → ‖Y‖ < r' →
      (∑' m : ℕ × ℕ, Φ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.2 : ℤ)) *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁' + (m.1 : ℤ))))) * X ^ m.1 * Y ^ m.2) * (D₁'.eval X * D₂'.eval Y) =
        MvPolynomial.eval ![X, Y] P') :
    ∀ X Y : ℂ, X ≠ 0 → Y ≠ 0 →
      X ^ N₁ * Y ^ N₁ * MvPolynomial.eval ![X, Y] P * (D₁'.eval X * D₂'.eval Y) =
        X ^ N₁' * Y ^ N₁' * MvPolynomial.eval ![X, Y] P' * (D₁.eval X * D₂.eval Y) := by

  have hL : LRep fun X Y => X ^ N₁ * Y ^ N₁ * MvPolynomial.eval ![X, Y] P * (D₁'.eval X * D₂'.eval Y) :=
    (((LRep.zpow_fst N₁).mul (LRep.zpow_snd N₁)).mul (LRep.mvPolynomial_eval_self P)).mul
      ((LRep.fst.polynomial_eval D₁').mul (LRep.snd.polynomial_eval D₂'))
  have hR : LRep fun X Y => X ^ N₁' * Y ^ N₁' * MvPolynomial.eval ![X, Y] P' * (D₁.eval X * D₂.eval Y) :=
    (((LRep.zpow_fst N₁').mul (LRep.zpow_snd N₁')).mul (LRep.mvPolynomial_eval_self P')).mul
      ((LRep.fst.polynomial_eval D₁).mul (LRep.snd.polynomial_eval D₂))
  have hρ : 0 < min r r' := lt_min hr hr'
  refine LRep.eq_of_forall_mem hL hR {x : ℂ | x ≠ 0 ∧ ‖x‖ < min r r'} {x : ℂ | x ≠ 0 ∧ ‖x‖ < min r r'}
    (infinite_puncturedBall hρ) (infinite_puncturedBall hρ) (fun x hx => hx.1) (fun y hy => hy.1)
    fun X hX Y hY => ?_
  obtain ⟨hX0, hX⟩ := hX
  obtain ⟨hY0, hY⟩ := hY
  rw [lt_min_iff] at hX hY
  rcases le_total N₁ N₁' with hle | hle
  · exact torus_cleared_eq_of_le_of_small v hπ Φ N₁ D₁ D₂ P r N₁' D₁' D₂' P' r' hle h hsupp' h' X Y hX0 hY0
      hX.1 hY.1 hX.2 hY.2
  · exact (torus_cleared_eq_of_le_of_small v hπ Φ N₁' D₁' D₂' P' r' N₁ D₁ D₂ P r hle h' hsupp h X Y hX0 hY0
      hX.2 hY.2 hX.1 hY.1).symm

end Ws1.Middle.TorusUnique
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace Ws1
namespace Middle

theorem exists_middle_of_halves (q ε : ℂ) (Z D E₁ E₂ Ed₁ Ed₂ : ℂ → ℂ)
    (m₁P m₂P : Polynomial ℂ) (kP : ℤ) (σP : ℝ) (hm₂P : m₂P ≠ 0)
    (hP : ∀ s : ℂ, σP < s.re →
      Z s * E₁ s * E₂ s * m₂P.eval (q ^ (-s)) = m₁P.eval (q ^ (-s)) * q ^ ((kP : ℂ) * s))
    (m₁d m₂d : Polynomial ℂ) (kd : ℤ) (σD : ℝ) (hm₂d : m₂d ≠ 0)
    (hD : ∀ s : ℂ, σD < (1 - s).re →
      D s * Ed₁ s * Ed₂ s * m₂d.eval (q ^ (-s)) = m₁d.eval (q ^ (-s)) * q ^ ((kd : ℂ) * s))
    (hG : ∀ s : ℂ, m₁d.eval (q ^ (-s)) * q ^ ((kd : ℂ) * s) * m₂P.eval (q ^ (-s)) =
      ε ^ 2 * (m₁P.eval (q ^ (-s)) * q ^ ((kP : ℂ) * s)) * m₂d.eval (q ^ (-s))) :
    ∃ (m₁ m₂ : Polynomial ℂ) (k : ℤ) (σP σD : ℝ), m₂ ≠ 0 ∧
      (∀ s : ℂ, σP < s.re →
        Z s * E₁ s * E₂ s * m₂.eval (q ^ (-s)) = m₁.eval (q ^ (-s)) * q ^ ((k : ℂ) * s)) ∧
      (∀ s : ℂ, σD < (1 - s).re →
        D s * Ed₁ s * Ed₂ s * m₂.eval (q ^ (-s)) = ε ^ 2 * (m₁.eval (q ^ (-s)) * q ^ ((k : ℂ) * s))) := by
  refine ⟨m₁P * m₂d, m₂P * m₂d, kP, σP, σD, mul_ne_zero hm₂P hm₂d, fun s hs => ?_, fun s hs => ?_⟩
  · rw [Polynomial.eval_mul, Polynomial.eval_mul]
    linear_combination (m₂d.eval (q ^ (-s))) * hP s hs
  · rw [Polynomial.eval_mul, Polynomial.eval_mul]
    linear_combination (m₂P.eval (q ^ (-s))) * hD s hs + hG s

def IsTorusDatum (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (Φ : LocalGL3 v → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ) : Prop :=
    let A : ℤ × ℤ → ℂ := fun n =>
      Φ (iotaGL (UnramifiedWhittaker.scalarPi
            (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
    (
      D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧ 0 < r ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
        Summable (fun m : ℕ × ℕ => ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
        (∑' m : ℕ × ℕ, A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
          MvPolynomial.eval ![X, Y] P)

def torusNum (N₁ : ℤ) (P : MvPolynomial (Fin 2) ℂ) (X Y : ℂ) : ℂ := X ^ N₁ * Y ^ N₁ * MvPolynomial.eval ![X, Y] P

def torusDen (D₁ D₂ : Polynomial ℂ) (X Y : ℂ) : ℂ := D₁.eval X * D₂.eval Y

theorem torusDatum_unique (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (Φ : LocalGL3 v → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ)
    (N₁' : ℤ) (D₁' D₂' : Polynomial ℂ) (P' : MvPolynomial (Fin 2) ℂ) (r' : ℝ)
    (h : IsTorusDatum v hπ Φ N₁ D₁ D₂ P r) (h' : IsTorusDatum v hπ Φ N₁' D₁' D₂' P' r') :
    ∀ X Y : ℂ, X ≠ 0 → Y ≠ 0 →
      torusNum N₁ P X Y * torusDen D₁' D₂' X Y = torusNum N₁' P' X Y * torusDen D₁ D₂ X Y := by
  intro X Y hX hY
  obtain ⟨-, -, hr, hsupp, hXY⟩ := h
  obtain ⟨-, -, hr', hsupp', hXY'⟩ := h'
  simp only [torusNum, torusDen]
  exact Ws1.Middle.TorusUnique.torus_cleared_eq v hπ Φ N₁ D₁ D₂ P r hr hsupp
    (fun X Y hX hY => (hXY X Y hX hY).2) N₁' D₁' D₂' P' r' hr' hsupp' (fun X Y hX hY => (hXY' X Y hX hY).2)
    X Y hX hY

def IsMiddleDatumNF (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (Φb Φt : LocalGL3 v → ℂ) (X Y cNum wtN wtD : ℂ → ℂ) (m₁ m₂ : Polynomial ℂ) (k : ℤ) : Prop :=
  ∀ (Nb : ℤ) (Db₁ Db₂ : Polynomial ℂ) (Pb : MvPolynomial (Fin 2) ℂ) (rb : ℝ),
    IsTorusDatum v hπ Φb Nb Db₁ Db₂ Pb rb →
  ∀ (Nt : ℤ) (Dt₁ Dt₂ : Polynomial ℂ) (Pt : MvPolynomial (Fin 2) ℂ) (rt : ℝ),
    IsTorusDatum v hπ Φt Nt Dt₁ Dt₂ Pt rt →
  ∀ s : ℂ,
    m₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℂ) * s) *
        (torusDen Db₁ Db₂ (X s) (Y s) * torusDen Dt₁ Dt₂ (X s) (Y s) * wtD s) =
      m₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * cNum s *
        (torusNum Nb Pb (X s) (Y s) * torusDen Dt₁ Dt₂ (X s) (Y s) * wtD s +
          wtN s * torusNum Nt Pt (X s) (Y s) * torusDen Db₁ Db₂ (X s) (Y s))

def dualX (v : HeightOneSpectrum (𝓞 ℚ)) (α₁ : ℂ) (s : ℂ) : ℂ := α₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)

def dualY (v : HeightOneSpectrum (𝓞 ℚ)) (α₀ ωϖ : ℂ) (s : ℂ) : ℂ := α₀ * ωϖ⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s

def dualWtN (v : HeightOneSpectrum (𝓞 ℚ)) (_s : ℂ) : ℂ := (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((Ideal.absNorm v.asIdeal : ℂ))⁻¹

def dualWtD (v : HeightOneSpectrum (𝓞 ℚ)) (_s : ℂ) : ℂ := 1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹

def dualCNum (v : HeightOneSpectrum (𝓞 ℚ)) (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ) (a₁' a₂' C₀ : ℂ) (s : ℂ) : ℂ :=
  C₀ * ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) *
    E.eval (a₁' * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval (a₂'⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))

def dualAlpha0 (v : HeightOneSpectrum (𝓞 ℚ)) (a₂' : ℂ) : ℂ := (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * a₂'⁻¹

def dualAlpha1 (v : HeightOneSpectrum (𝓞 ℚ)) (a₁' : ℂ) : ℂ := (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * a₁'⁻¹

def dualC0 (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) (a₁' a₂' : ℂ) (cK μ₀ μ₁ : ℂ) : ℂ :=
  cK * μ₀ * μ₁ ^ 2 * (μ₀ * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * a₁' * a₂'⁻¹))⁻¹ * ((dualAlpha1 v a₁') ^ ℓ)⁻¹

def IsDualMiddleDatum (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (V : LocalGL3 v → ℂ) (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ) (a₁' a₂' ωϖ cK μ₀ μ₁ : ℂ)
    (m₁ m₂ : Polynomial ℂ) (k : ℤ) : Prop :=
  IsMiddleDatumNF v hπ
    (fun x => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ)))))
    (fun x => V (x * (longWeyl3 * weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ)))))
    (dualX v (dualAlpha1 v a₁')) (dualY v (dualAlpha0 v a₂') ωϖ)
    (dualCNum v E Ed ε ℓ a₁' a₂' (dualC0 v ℓ a₁' a₂' cK μ₀ μ₁)) (dualWtN v) (dualWtD v) m₁ m₂ k

def primalX (v : HeightOneSpectrum (𝓞 ℚ)) (β₀ : ℂ) (s : ℂ) : ℂ := β₀ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)

def primalY (v : HeightOneSpectrum (𝓞 ℚ)) (β₁ ωϖ : ℂ) (s : ℂ) : ℂ := β₁⁻¹ * ωϖ⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s

def primalWtN (v : HeightOneSpectrum (𝓞 ℚ)) (_s : ℂ) : ℂ := 1

def primalWtD (v : HeightOneSpectrum (𝓞 ℚ)) (_s : ℂ) : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

def primalCNum (v : HeightOneSpectrum (𝓞 ℚ)) (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (a₁' a₂' C₀ : ℂ) (s : ℂ) : ℂ :=
  C₀ * ε⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((ℓ : ℂ) / 2)) * (a₂' * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (-(ℓ : ℤ)) *
    E.eval (a₁' * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval (a₂'⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))

def primalBeta0 (v : HeightOneSpectrum (𝓞 ℚ)) (a₁' : ℂ) : ℂ := a₁' * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))

def primalBeta1 (v : HeightOneSpectrum (𝓞 ℚ)) (a₂' : ℂ) : ℂ := a₂' * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))

def primalC0 (v : HeightOneSpectrum (𝓞 ℚ)) (a₁' a₂' : ℂ) (cK μ₀ μ₁ : ℂ) : ℂ :=
  cK * μ₀ ^ 2 * μ₀ * μ₁ ^ 2 * (μ₀ * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * a₁' * a₂'⁻¹))⁻¹

def IsPrimalMiddleDatum (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (V : LocalGL3 v → ℂ) (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ) (a₁' a₂' ωϖ cK μ₀ μ₁ : ℂ)
    (m₁ m₂ : Polynomial ℂ) (k : ℤ) : Prop :=
  IsMiddleDatumNF v hπ
    (fun x => V (x * (longWeyl3 * weylPrime3)))
    (fun x => V (x * weylPrime3))
    (primalX v (primalBeta0 v a₁')) (primalY v (primalBeta1 v a₂') ωϖ)
    (primalCNum v E Ed ε ℓ a₁' a₂' (primalC0 v a₁' a₂' cK μ₀ μ₁)) (primalWtN v) (primalWtD v) m₁ m₂ k

end Ws1.Middle
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp AutomorphicForm~lowerUnipotentGL2"

namespace Ws1
namespace DualPoint

variable {K : Type*} [Field K]

theorem iotaGL_diagUnitGL2_mul_weylPrime3_transposeInv3 (t a : Kˣ) (y : K) :
    iotaGL (diagUnitGL2 t) * ((weylPrime3 : GL (Fin 3) K) * transposeInv3 (iotaGL (diagUnits2 1 a * unipotentGL2 y))) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) a⁻¹ * iotaGL (diagUnits2 (t * a) a) *
        ((weylPrime3 : GL (Fin 3) K) * lowerUnipotent21 (-y)) := by
  apply Units.ext
  have ha : (a : K) ≠ 0 := a.ne_zero
  have hinv : (((iotaGL (diagUnits2 1 a * unipotentGL2 y) : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, -y * (a : K)⁻¹, 0; 0, (a : K)⁻¹, 0; 0, 0, 1] := by
    rw [Matrix.coe_units_inv]
    refine Matrix.inv_eq_left_inv ?_
    simp only [coe_iotaGL, Units.val_mul, coe_diagUnits2, unipotentGL2_coe, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, ha]
  have hT : (transposeInv3 (iotaGL (diagUnits2 1 a * unipotentGL2 y)) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; -y * (a : K)⁻¹, (a : K)⁻¹, 0; 0, 0, 1] := by
    rw [Ws1.Middle.DualKit.transposeInv3_coe, hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, coe_diagUnits2, hT, lowerUnipotent21_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, weylPrime3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.GeneralLinearGroup.scalar, ha] <;>
    field_simp

end Ws1.DualPoint
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace Ws1
namespace Middle
namespace DualD23

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev Fv : Type := v.adicCompletion ℚ

abbrev G2 : Type := GL (Fin 2) (v.adicCompletion ℚ)

abbrev K2 : Subgroup (G2 v) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤

theorem isLocalLevelOne_top_of_integral {m : Matrix (Fin 2) (Fin 2) (Fv v)}
    (h : ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : Fv v)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_K2_iff (k : G2 v) :
    k ∈ K2 v ↔ (∀ i j, (k : Matrix (Fin 2) (Fin 2) (Fv v)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      ∀ i j, ((k⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) i j ∈ v.adicCompletionIntegers ℚ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral v h1, isLocalLevelOne_top_of_integral v h2⟩

theorem mem_K2_of_entries {k : G2 v}
    (h : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((k⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1) : k ∈ K2 v :=
  (mem_K2_iff v k).mpr ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h i j),
    fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h' i j)⟩

def lowerUnipotentGL2 (x : Fv v) : G2 v :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_lowerUnipotentGL2 (x : Fv v) :
    ((lowerUnipotentGL2 v x : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; x, 1] := rfl

theorem coe_inv_lowerUnipotentGL2 (x : Fv v) :
    (((lowerUnipotentGL2 v x)⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; -x, 1] := rfl

theorem coe_inv_unipotentGL2 (x : Fv v) :
    (((unipotentGL2 x : G2 v)⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, -x; 0, 1] := rfl

private theorem _root_.Ws1.Middle.DualD23.unipotentGL2_mem_K2 {y : Fv v} (hy : Valued.v y ≤ 1) : (unipotentGL2 y : G2 v) ∈ K2 v := by
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [coe_inv_unipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hy, Valuation.map_neg]

p2m_export "Ws1.Middle.DualD23" "unipotentGL2_mem_K2"
theorem lowerUnipotentGL2_mem_K2 {x : Fv v} (hx : Valued.v x ≤ 1) : lowerUnipotentGL2 v x ∈ K2 v := by
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [coe_lowerUnipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [coe_inv_lowerUnipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hx, Valuation.map_neg]

private theorem _root_.Ws1.Middle.DualD23.w0_mem_K2 {w₀ : G2 v} (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0]) : w₀ ∈ K2 v := by
  have hinv : ((w₀⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0] := by
    rw [Matrix.coe_units_inv, hw₀]
    refine Matrix.inv_eq_left_inv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [hw₀]; fin_cases i <;> fin_cases j <;> simp
  · rw [hinv]; fin_cases i <;> fin_cases j <;> simp

p2m_export "Ws1.Middle.DualD23" "w0_mem_K2"

section Inst

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

scoped instance borelSpace_units_adic : BorelSpace (Fv v)ˣ := borelSpace_units

scoped instance secondCountable_units_adic : SecondCountableTopology (Fv v)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

private scoped instance _root_.Ws1.Middle.DualD23.isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

p2m_export "Ws1.Middle.DualD23" "isAddHaarMeasure_selfDualHaarAt"
scoped instance isHaarMeasure_mulHaar :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure (Fv v)ˣ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure ℚ v (selfDualHaarAt ℚ v)

theorem one_lt_q : 1 < Ideal.absNorm v.asIdeal := by
  refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot, ?_⟩
  exact Ideal.absNorm_eq_one_iff.not.mpr (Ideal.IsPrime.ne_top v.isPrime)

theorem one_lt_qR : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_q v

theorem qR_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one (one_lt_qR v)

theorem qC_ne_zero : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

theorem qC_eq : (Ideal.absNorm v.asIdeal : ℂ) = ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) := by norm_cast

theorem norm_qC_cpow (S : ℂ) :
    ‖(Ideal.absNorm v.asIdeal : ℂ) ^ S‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ S.re := by
  rw [qC_eq, Complex.norm_cpow_eq_rpow_re_of_pos (qR_pos v)]

end Inst
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

section Cyc

variable {v} {W₃ : LocalGL3 v → ℂ}

private theorem _root_.Ws1.Middle.DualD23.law_of_mem_gl3CyclicSubspace {θ : AddChar (Fv v) ℂ}
    (hW₃law : IsGL3PsiWhittakerFn θ W₃) {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    IsGL3PsiWhittakerFn θ W := by
  have hle : gl3CyclicSubspace W₃ ≤ gl3PsiWhittakerFnSpace (Fv v) ℂ θ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace θ h ((mem_gl3PsiWhittakerFnSpace_iff θ _).mpr hW₃law)
  exact (mem_gl3PsiWhittakerFnSpace_iff θ _).mp (hle hW)

p2m_export "Ws1.Middle.DualD23" "law_of_mem_gl3CyclicSubspace"
theorem central_of_mem_gl3CyclicSubspace {ω : (Fv v)ˣ →* ℂˣ}
    (hω : ∀ (z : (Fv v)ˣ) (g : LocalGL3 v),
      W₃ (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W₃ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    ∀ (z : (Fv v)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g := by
  refine Submodule.span_induction (p := fun W _ => ∀ (z : (Fv v)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ z g
    simp only [gl3AmbientRightTranslate_apply]
    rw [mul_assoc, hω]
  · intro z g; simp
  · intro f g _ _ hf hg z x
    simp only [Pi.add_apply]
    rw [hf, hg]; ring
  · intro a f _ hf z x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]; ring

private theorem _root_.Ws1.Middle.DualD23.smooth_of_mem_gl3CyclicSubspace
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
      W₃ (g * k) = W₃ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
      W (g * k) = W g := by
  refine Submodule.span_induction (p := fun W _ =>
      ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
        W (g * k) = W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩
    obtain ⟨Uv, hUv, hinv⟩ := hW₃sm
    let φ : LocalGL3 v →* LocalGL3 v := (MulAut.conj h⁻¹).toMonoidHom
    refine ⟨Uv.comap φ, ?_, ?_⟩
    · have hφ : Continuous φ := by
        change Continuous fun x : LocalGL3 v => h⁻¹ * x * h⁻¹⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const
      exact hUv.preimage hφ
    · intro k hk g
      have hk' : h⁻¹ * k * h ∈ Uv := by
        have := hk
        rw [Subgroup.mem_comap] at this
        simpa [φ] using this
      simp only [gl3AmbientRightTranslate_apply]
      have : g * k * h = g * h * (h⁻¹ * k * h) := by group
      rw [this, hinv _ hk']
  · obtain ⟨Uv, hUv, _⟩ := hW₃sm
    exact ⟨Uv, hUv, fun k _ g => rfl⟩
  · rintro f g _ _ ⟨U₁, hU₁, h₁⟩ ⟨U₂, hU₂, h₂⟩
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk x => ?_⟩
    · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
    · simp only [Pi.add_apply]
      rw [h₁ k (Subgroup.mem_inf.mp hk).1, h₂ k (Subgroup.mem_inf.mp hk).2]
  · rintro a f _ ⟨U, hU, h⟩
    exact ⟨U, hU, fun k hk x => by simp only [Pi.smul_apply, smul_eq_mul]; rw [h k hk]⟩

p2m_export "Ws1.Middle.DualD23" "smooth_of_mem_gl3CyclicSubspace"
end Cyc
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

def ordU (u : (Fv v)ˣ) : ℤ := -WithZero.log (Valued.v (u : Fv v))

theorem valued_eq_exp_neg_ordU (u : (Fv v)ˣ) : Valued.v (u : Fv v) = WithZero.exp (-ordU v u) := by
  rw [ordU, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr u.ne_zero)]

theorem ordU_mul (a b : (Fv v)ˣ) : ordU v (a * b) = ordU v a + ordU v b := by
  simp only [ordU, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr a.ne_zero) ((Valuation.ne_zero_iff _).mpr b.ne_zero)]
  ring

theorem ordU_one : ordU v 1 = 0 := by simp [ordU]

theorem ordU_eq_zero_of_valued_eq_one {u : (Fv v)ˣ} (hu : Valued.v (u : Fv v) = 1) : ordU v u = 0 := by
  simp [ordU, hu]

theorem ordU_mk0_eq_one {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    ordU v (Units.mk0 π hπ) = 1 := by
  simp [ordU, hϖ]

def unrChar (c : ℂˣ) : (Fv v)ˣ →* ℂˣ where
  toFun u := c ^ ordU v u
  map_one' := by rw [ordU_one, zpow_zero]
  map_mul' a b := by rw [ordU_mul, zpow_add]

theorem unrChar_apply (c : ℂˣ) (u : (Fv v)ˣ) : unrChar v c u = c ^ ordU v u := rfl

theorem unrChar_eq_one_of_valued_eq_one (c : ℂˣ) {u : (Fv v)ˣ} (hu : Valued.v (u : Fv v) = 1) :
    unrChar v c u = 1 := by
  rw [unrChar_apply, ordU_eq_zero_of_valued_eq_one v hu, zpow_zero]

theorem unrChar_mk0 (c : ℂˣ) {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    unrChar v c (Units.mk0 π hπ) = c := by
  rw [unrChar_apply, ordU_mk0_eq_one v hπ hϖ, zpow_one]

def w0 : G2 v :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_w0 : ((w0 v : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0] := rfl

section Signs

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

def dNeg : G2 v := diagonal2 v ![1, -1]

def dNeg' : G2 v := diagonal2 v ![-1, 1]

theorem coe_dNeg : ((dNeg v : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; 0, -1] := by
  show Matrix.diagonal _ = _
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem coe_dNeg' : ((dNeg' v : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![-1, 0; 0, 1] := by
  show Matrix.diagonal _ = _
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem dNeg_mul_dNeg : dNeg v * dNeg v = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_dNeg, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_inv_dNeg : (((dNeg v)⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; 0, -1] := by
  rw [inv_eq_of_mul_eq_one_right (dNeg_mul_dNeg v), coe_dNeg]

theorem dNeg_mem_K2 : dNeg v ∈ K2 v := by
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [coe_dNeg]; fin_cases i <;> fin_cases j <;> simp
  · rw [coe_inv_dNeg]; fin_cases i <;> fin_cases j <;> simp

theorem dNeg_mul_unipotent (x : Fv v) : dNeg v * unipotent x = unipotent (-x) * dNeg v := by
  apply Units.ext
  simp only [Units.val_mul, coe_dNeg, UnramifiedWhittaker.unipotent, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem w0_unipotentGL2_dNeg (y : Fv v) :
    w0 v * unipotentGL2 y * dNeg v = dNeg' v * (w0 v * unipotentGL2 (-y)) := by
  apply Units.ext
  simp only [Units.val_mul, coe_dNeg, coe_dNeg', coe_w0, unipotentGL2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dNeg_mul_scalarPi {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) :
    dNeg v * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ =
      scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ * dNeg v := by
  apply Units.ext
  simp only [Units.val_mul, coe_dNeg, UnramifiedWhittaker.scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dNeg_mul_diagZ {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (m : ℤ) :
    dNeg v * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m =
      diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m * dNeg v := by
  apply Units.ext
  simp only [Units.val_mul, coe_dNeg, UnramifiedWhittaker.diagZ, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem apply_dNeg'_mul {χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hχ : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χ i e = 1)
    {f : G2 v → ℂ} (hf : f ∈ principalSeries2 v χ) (g : G2 v) :
    f (dNeg' v * g) = f g := by
  have h := hf.2.2 (![-1, 1]) g
  rw [show diagonal2 v ![-1, 1] = dNeg' v from rfl] at h
  rw [h]
  have h1 : torusChar2 v χ ![-1, 1] = 1 := by
    simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      map_one, Units.val_one, mul_one]
    rw [hχ 0 (-1) (by rw [Units.val_neg, Units.val_one, Valuation.map_neg, Valuation.map_one]), Units.val_one]
  have h2 : halfModulus2 v ![-1, 1] = 1 := by
    simp [halfModulus2]
  rw [h1, h2, one_mul, one_mul]

scoped instance regular_selfDualHaarAt : (selfDualHaarAt ℚ v).Regular := by
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)
    with hc
  have hdef : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  rw [hdef]
  exact Measure.Regular.smul ENNReal.coe_ne_top

end Signs
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

section Flip

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem jacquet_flip (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    {χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hχ : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χ i e = 1)
    {f : G2 v → ℂ} (hf : f ∈ principalSeries2 v χ) (g : G2 v) :
    ∫ y, f (w0 v * unipotentGL2 y * g) * ψv⁻¹ y ∂(selfDualHaarAt ℚ v) =
      ∫ y, f (w0 v * unipotentGL2 y * (dNeg v * g)) * (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ y
        ∂(selfDualHaarAt ℚ v) := by
  rw [← integral_neg_eq_self (fun y => f (w0 v * unipotentGL2 y * (dNeg v * g)) *
    (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ y) (selfDualHaarAt ℚ v)]
  congr 1
  funext y
  have hmat : w0 v * unipotentGL2 (-y) * (dNeg v * g) = dNeg' v * (w0 v * unipotentGL2 y * g) := by
    rw [← mul_assoc, w0_unipotentGL2_dNeg, neg_neg, mul_assoc]
  rw [hmat, apply_dNeg'_mul v hχ hf, hψinv, AddChar.inv_apply, AddChar.inv_apply]

end Flip
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

section D2

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem sectionRep_dual {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0) (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) (u : ℂ)
    (hu : ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) < ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re)
    (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)))
        ((Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u))) m) :
    ∃ (α₀ α₁ : ℂ) (_ : α₀ ≠ 0 ∧ α₁ ≠ 0) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
      (_ : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
      (_ : ((χD 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₀)
      (_ : ((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₁)
      (_ : α₀ * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) ∧ α₁ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2))
      (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (_ : fD ∈ principalSeries2 v χD)
      (_ : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → fD (g * k) = fD g)
      (_ : fD 1 = ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) *
        (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹)
      (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (_ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0]),
      W₂d = fun g => ∫ y, fD (w₀ * unipotentGL2 y * g) * ψv⁻¹ y ∂(selfDualHaarAt ℚ v) := by

  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := qC_ne_zero v
  have hNcpow : ∀ w : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ w ≠ 0 := fun w h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have ha₁ : a₁ ≠ 0 := left_ne_zero_of_mul ha
  have ha₂ : a₂ ≠ 0 := right_ne_zero_of_mul ha
  set a₁' : ℂ := a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u) with ha₁'
  set a₂' : ℂ := a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u with ha₂'
  have ha₁'0 : a₁' ≠ 0 := mul_ne_zero ha₁ (hNcpow _)
  have ha₂'0 : a₂' ≠ 0 := mul_ne_zero ha₂ (hNcpow _)
  set α₀ : ℂ := (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * a₂'⁻¹ with hα₀
  set α₁ : ℂ := (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * a₁'⁻¹ with hα₁
  have hα₀0 : α₀ ≠ 0 := mul_ne_zero (hNcpow _) (inv_ne_zero ha₂'0)
  have hα₁0 : α₁ ≠ 0 := mul_ne_zero (hNcpow _) (inv_ne_zero ha₁'0)
  have hhalf : (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) = (Ideal.absNorm v.asIdeal : ℂ) := by
    rw [← Complex.cpow_add _ _ hN0, show ((1 : ℂ) / 2) + (1 / 2) = 1 by ring, Complex.cpow_one]

  obtain ⟨χ, hχ⟩ : ∃ χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ),
      χ = ![unrChar v (Units.mk0 _ hα₀0), unrChar v (Units.mk0 _ hα₁0)] := ⟨_, rfl⟩
  have hχunr : ∀ i, ∀ w : (v.adicCompletion ℚ)ˣ, Valued.v (w : v.adicCompletion ℚ) = 1 → χ i w = 1 := by
    intro i w hw
    rw [hχ]
    fin_cases i <;> exact unrChar_eq_one_of_valued_eq_one v _ hw
  have hχ0 : ((χ 0 (Units.mk0 _ hπ) : ℂˣ) : ℂ) = α₀ := by
    rw [hχ]; exact congrArg Units.val (unrChar_mk0 v _ hπ hϖ)
  have hχ1 : ((χ 1 (Units.mk0 _ hπ) : ℂˣ) : ℂ) = α₁ := by
    rw [hχ]; exact congrArg Units.val (unrChar_mk0 v _ hπ hϖ)

  have hNR : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := qR_pos v
  have hnorm' : ∀ a w : ℂ, ‖a * (Ideal.absNorm v.asIdeal : ℂ) ^ w‖ = ‖a‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ w.re := by
    intro a w; rw [norm_mul, norm_qC_cpow]
  have ha₁'lt : ‖a₁'‖ < ‖a₂'‖ := by
    rw [ha₁', ha₂', hnorm', hnorm', Complex.neg_re]
    exact_mod_cast hu
  have hdom : ‖((χ 0 (Units.mk0 _ hπ) : ℂˣ) : ℂ)‖ < ‖((χ 1 (Units.mk0 _ hπ) : ℂˣ) : ℂ)‖ := by
    rw [hχ0, hχ1, hα₀, hα₁, norm_mul, norm_mul, norm_inv, norm_inv]
    have hp : 0 < ‖(Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2)‖ := norm_pos_iff.mpr (hNcpow _)
    refine mul_lt_mul_of_pos_left ?_ hp
    exact (inv_lt_inv₀ (norm_pos_iff.mpr ha₂'0) (norm_pos_iff.mpr ha₁'0)).mpr ha₁'lt

  obtain ⟨f, hf, hfK, hf1⟩ :=
    LanglandsTunnell.CubicInduction.exists_spherical_mem_principalSeries2_of_unramified v χ hχunr
  have hS := LanglandsTunnell.CubicInduction.jacquetIntegral_spherical_laws_of_unramified_of_norm_lt v hπ hϖ χ hχunr
    hdom f hf hfK hf1 (w0 v) (coe_w0 v) (selfDualHaarAt ℚ v)
  obtain ⟨J, hJ⟩ : ∃ J : GL (Fin 2) (v.adicCompletion ℚ) → ℂ, J = fun g =>
      ∫ y, f (w0 v * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ y
        ∂(selfDualHaarAt ℚ v) := ⟨_, rfl⟩
  obtain ⟨-, hJψ, hJK, hJZ, hJ1val, hJ1ne, hJT⟩ := hS
  have hJψ' : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      J (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * J g := by
    intro x g; rw [hJ]; exact hJψ x g
  have hJK' : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
      J (g * k) = J g := by
    intro k g hk; rw [hJ]; exact hJK k g hk
  have hJZ' : ∀ g : GL (Fin 2) (v.adicCompletion ℚ), J (g * scalarPi _ hπ) = α₀ * α₁ * J g := by
    intro g; rw [hJ, ← hχ0, ← hχ1]; exact hJZ g
  have hJ1' : J 1 ≠ 0 := by rw [hJ]; exact hJ1ne
  have hJT' : ∀ m : ℤ, J (diagZ _ hπ m) = J 1 * torusFactor (Ideal.absNorm v.asIdeal : ℂ)
      ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (α₀ + α₁)) (α₀ * α₁) m := by
    intro m; rw [hJ, ← hχ0, ← hχ1]; exact hJT m

  have hαprod : α₀ * α₁ = (Ideal.absNorm v.asIdeal : ℂ) / (a₁' * a₂') := by
    rw [hα₀, hα₁]
    calc (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * a₂'⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * a₁'⁻¹)
        = ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2)) * (a₂'⁻¹ * a₁'⁻¹) := by ring
      _ = _ := by rw [hhalf]; field_simp
  have hαsum : (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (α₀ + α₁) = (Ideal.absNorm v.asIdeal : ℂ) * (a₁' + a₂') / (a₁' * a₂') := by
    rw [hα₀, hα₁]
    calc (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * a₂'⁻¹ + (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * a₁'⁻¹)
        = ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2)) * (a₂'⁻¹ + a₁'⁻¹) := by ring
      _ = _ := by rw [hhalf]; field_simp

  set Wc : GL (Fin 2) (v.adicCompletion ℚ) → ℂ := fun g => (J 1)⁻¹ * J (dNeg v * g) with hWc
  have hWcψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      Wc (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * Wc g := by
    intro x g
    show (J 1)⁻¹ * J (dNeg v * (unipotent x * g)) = _ * ((J 1)⁻¹ * J (dNeg v * g))
    rw [← mul_assoc, dNeg_mul_unipotent, mul_assoc, hJψ', AddChar.inv_apply]
    ring
  have hWcK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
      Wc (g * k) = Wc g := by
    intro k g hk
    show (J 1)⁻¹ * J (dNeg v * (g * k)) = (J 1)⁻¹ * J (dNeg v * g)
    rw [← mul_assoc, hJK' k _ hk]
  have hWcZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ), Wc (g * scalarPi _ hπ) =
      (Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) * Wc g := by
    intro g
    show (J 1)⁻¹ * J (dNeg v * (g * scalarPi _ hπ)) = _ * ((J 1)⁻¹ * J (dNeg v * g))
    rw [← mul_assoc, hJZ', hαprod]
    ring
  have hWcT : ∀ m : ℤ, Wc (diagZ _ hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)))
        ((Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u))) m := by
    intro m
    show (J 1)⁻¹ * J (dNeg v * diagZ _ hπ m) = _
    rw [dNeg_mul_diagZ, hJK' _ _ (dNeg_mem_K2 v), hJT', inv_mul_cancel_left₀ hJ1', hαsum, hαprod]
  have hW₂eq : W₂d = Wc :=
    UnramifiedWhittaker.eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ v hπ hϖ
      (((NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ : AddChar (v.adicCompletion ℚ) ℂ) : v.adicCompletion ℚ → ℂ)
      _ _ W₂d Wc hW₂dψ hW₂dK hW₂dZ hW₂dT hWcψ hWcK hWcZ hWcT

  refine ⟨α₀, α₁, ⟨hα₀0, hα₁0⟩, χ, hχunr, hχ0, hχ1, ⟨?_, ?_⟩, (J 1)⁻¹ • f,
    Submodule.smul_mem _ _ hf, fun k g hk => ?_, ?_, w0 v, coe_w0 v, ?_⟩
  · rw [hα₀]; field_simp
  · rw [hα₁]; field_simp
  · show (J 1)⁻¹ * f (g * k) = (J 1)⁻¹ * f g
    rw [hfK k g hk]
  · show (J 1)⁻¹ * f 1 = _
    have hJ1v : J 1 = ((((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal : ℝ) : ℂ) *
        (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * α₀ / α₁) := by
      rw [hJ, ← hχ0, ← hχ1]; exact hJ1val
    rw [hf1, mul_one, hJ1v]
    congr 1
    show _ = (((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal : ℂ) * _
    congr 1
    have h12 : (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) ≠ 0 := hNcpow _
    rw [hα₀, hα₁]
    field_simp
  · rw [hW₂eq]
    funext g
    show (J 1)⁻¹ * J (dNeg v * g) = ∫ y, (J 1)⁻¹ * f (w0 v * unipotentGL2 y * g) * ψv⁻¹ y ∂(selfDualHaarAt ℚ v)
    simp only [hJ]
    rw [← jacquet_flip v ψv hψinv hχunr hf g, ← integral_const_mul]
    congr 1
    funext y
    ring

end D2
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

section D3

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

private theorem _root_.Ws1.Middle.DualD23.transposeInv3_mul (x c : LocalGL3 v) : transposeInv3 (x * c) = transposeInv3 x * transposeInv3 c := by
  apply Units.ext
  show (((x * c)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).transpose =
    ((x⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).transpose *
      ((c⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

p2m_export "Ws1.Middle.DualD23" "transposeInv3_mul"

theorem gauge_dual_rightTranslate (W : LocalGL3 v → ℂ)
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W) (c : LocalGL3 v) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) →
        (fun x : LocalGL3 v => dualWhittakerFn3 V (x * c)) h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖(fun x : LocalGL3 v => dualWhittakerFn3 V (x * c)) h‖ ≤
          C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
  have heq : (fun x : LocalGL3 v => dualWhittakerFn3 V (x * c)) =
      dualWhittakerFn3 (gl3AmbientRightTranslate (R := ℂ) (transposeInv3 c) V) := by
    funext x
    simp only [dualWhittakerFn3_apply, gl3AmbientRightTranslate_apply]
    rw [transposeInv3_mul, mul_assoc]
  rw [heq]
  exact (LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
    W hWgauge _ (gl3AmbientRightTranslate_mem_gl3CyclicSubspace W (transposeInv3 c) hVmem)).2

theorem integrable_sectionForm_dual {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0) (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (Wt : LocalGL3 v → ℂ)
    (hWtsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, Wt (g * k) = Wt g)
    (hWtgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Wt h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖Wt h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχDu : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
    (hdom : ‖((χD 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)‖ < ‖((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)‖)
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (hfD : fD ∈ principalSeries2 v χD)
    (hfDK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → fD (g * k) = fD g)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure] :
    ∃ σc : ℝ, ∀ s : ℂ, σc < (1 - s).re →
      Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
        (Wt (iotaGL g) * fD (w₀ * g)) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
            ((1 - s) - 1 / 2)) μ₂ := by
  have hK2open : IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v ⊤ top_ne_bot).2
  obtain ⟨σ, hσ⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
      v Wt hWtsm hWtgauge χD (fun _ => 0) (fun i w hw => hχDu i w hw.1) (Units.mk0 _ hπ) hϖ hdom fD hfD
      ⟨_, hK2open, fun k hk g => hfDK k g hk⟩ w₀ hw₀ μ₂
  exact ⟨σ, fun s hs => hσ (1 - s) hs⟩

theorem dominance_of_alpha_eq (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) (u : ℂ)
    (hu : ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) < ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re)
    (α₀ α₁ : ℂ)
    (hα : α₀ * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) ∧ α₁ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2)) :
    ‖α₀‖ < ‖α₁‖ := by
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := qC_ne_zero v
  have hNcpow : ∀ w : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ w ≠ 0 := fun w h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have ha₁ : a₁ ≠ 0 := left_ne_zero_of_mul ha
  have ha₂ : a₂ ≠ 0 := right_ne_zero_of_mul ha
  have h1 : a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u) ≠ 0 := mul_ne_zero ha₁ (hNcpow _)
  have h2 : a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u ≠ 0 := mul_ne_zero ha₂ (hNcpow _)
  have e0 : α₀ = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ := by
    rw [← hα.1, mul_inv_cancel_right₀ h2]
  have e1 : α₁ = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ := by
    rw [← hα.2, mul_inv_cancel_right₀ h1]
  have hlt : ‖a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)‖ < ‖a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u‖ := by
    rw [norm_mul, norm_mul, norm_qC_cpow, norm_qC_cpow, Complex.neg_re]
    exact_mod_cast hu
  rw [e0, e1, norm_mul, norm_mul, norm_inv, norm_inv]
  exact mul_lt_mul_of_pos_left ((inv_lt_inv₀ (norm_pos_iff.mpr h2) (norm_pos_iff.mpr h1)).mpr hlt)
    (norm_pos_iff.mpr (hNcpow _))

end D3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

end Ws1.Middle.DualD23
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit"

open Finset Polynomial

namespace Ws1
namespace Middle
namespace Laurent1

def LRep1 (q : ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ (P : Polynomial ℂ) (M : ℕ), ∀ s : ℂ, f s * ((q : ℂ) ^ (-s)) ^ M = P.eval ((q : ℂ) ^ (-s))

section Atoms

variable {q : ℕ} (hq : 1 < q)
include hq

theorem qC_ne_zero : (q : ℂ) ≠ 0 := by exact_mod_cast (lt_trans zero_lt_one hq).ne'

theorem x_ne_zero (s : ℂ) : (q : ℂ) ^ (-s) ≠ 0 := by
  intro h; exact qC_ne_zero hq ((Complex.cpow_eq_zero_iff _ _).mp h).1

theorem cpow_ne_zero' (w : ℂ) : (q : ℂ) ^ w ≠ 0 := by
  intro h; exact qC_ne_zero hq ((Complex.cpow_eq_zero_iff _ _).mp h).1

theorem qs_eq_inv (s : ℂ) : (q : ℂ) ^ s = ((q : ℂ) ^ (-s))⁻¹ := by
  rw [Complex.cpow_neg, inv_inv]

theorem qs_mul_x (s : ℂ) : (q : ℂ) ^ s * (q : ℂ) ^ (-s) = 1 := by
  rw [qs_eq_inv hq, inv_mul_cancel₀ (x_ne_zero hq s)]

theorem q_one_sub (s : ℂ) : (q : ℂ) ^ (1 - s) = (q : ℂ) * (q : ℂ) ^ (-s) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ (qC_ne_zero hq), Complex.cpow_one]

theorem q_neg_add (a s : ℂ) : (q : ℂ) ^ (-(s + a)) = (q : ℂ) ^ (-a) * (q : ℂ) ^ (-s) := by
  rw [show -(s + a) = -a + -s by ring, Complex.cpow_add _ _ (qC_ne_zero hq)]

theorem q_neg_sub (a s : ℂ) : (q : ℂ) ^ (-(a - s)) = (q : ℂ) ^ (-a) * ((q : ℂ) ^ (-s))⁻¹ := by
  rw [show -(a - s) = -a + s by ring, Complex.cpow_add _ _ (qC_ne_zero hq)]
  congr 1
  exact qs_eq_inv hq s

theorem q_natMul_sub (n : ℕ) (a s : ℂ) :
    (q : ℂ) ^ ((n : ℂ) * (a - s)) = ((q : ℂ) ^ a) ^ n * ((q : ℂ) ^ (-s)) ^ n := by
  rw [Complex.cpow_nat_mul, sub_eq_add_neg, Complex.cpow_add _ _ (qC_ne_zero hq), mul_pow]

theorem qs_pow (j : ℕ) (s : ℂ) : ((q : ℂ) ^ s) ^ j = (q : ℂ) ^ ((j : ℂ) * s) := by
  rw [Complex.cpow_nat_mul]

end Atoms
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

section Closure

variable {q : ℕ} (hq : 1 < q)
include hq

private theorem _root_.Ws1.Middle.Laurent1.congr {f g : ℂ → ℂ} (hfg : ∀ s, f s = g s) (hf : LRep1 q f) : LRep1 q g := by
  obtain ⟨P, M, h⟩ := hf
  exact ⟨P, M, fun s => by rw [← hfg]; exact h s⟩

p2m_export "Ws1.Middle.Laurent1" "congr"
private theorem _root_.Ws1.Middle.Laurent1.const (c : ℂ) : LRep1 q (fun _ => c) :=
  ⟨Polynomial.C c, 0, fun s => by simp⟩

p2m_export "Ws1.Middle.Laurent1" "const"

theorem x : LRep1 q (fun s => (q : ℂ) ^ (-s)) :=
  ⟨Polynomial.X, 0, fun s => by simp⟩

theorem xinv : LRep1 q (fun s => (q : ℂ) ^ s) :=
  ⟨1, 1, fun s => by rw [pow_one, qs_mul_x hq, Polynomial.eval_one]⟩

theorem xinv' : LRep1 q (fun s => ((q : ℂ) ^ (-s))⁻¹) :=
  congr hq (fun s => qs_eq_inv hq s) (xinv hq)

private theorem _root_.Ws1.Middle.Laurent1.add {f g : ℂ → ℂ} (hf : LRep1 q f) (hg : LRep1 q g) : LRep1 q (fun s => f s + g s) := by
  obtain ⟨P, M, hP⟩ := hf
  obtain ⟨Q, N, hQ⟩ := hg
  refine ⟨P * Polynomial.X ^ N + Q * Polynomial.X ^ M, M + N, fun s => ?_⟩
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow,
    Polynomial.eval_X, ← hP s, ← hQ s]
  ring

p2m_export "Ws1.Middle.Laurent1" "add"
private theorem _root_.Ws1.Middle.Laurent1.mul {f g : ℂ → ℂ} (hf : LRep1 q f) (hg : LRep1 q g) : LRep1 q (fun s => f s * g s) := by
  obtain ⟨P, M, hP⟩ := hf
  obtain ⟨Q, N, hQ⟩ := hg
  refine ⟨P * Q, M + N, fun s => ?_⟩
  rw [Polynomial.eval_mul, ← hP s, ← hQ s]
  ring

p2m_export "Ws1.Middle.Laurent1" "mul"
private theorem _root_.Ws1.Middle.Laurent1.neg {f : ℂ → ℂ} (hf : LRep1 q f) : LRep1 q (fun s => -f s) := by
  obtain ⟨P, M, hP⟩ := hf
  exact ⟨-P, M, fun s => by rw [Polynomial.eval_neg, ← hP s]; ring⟩

p2m_export "Ws1.Middle.Laurent1" "neg"
private theorem _root_.Ws1.Middle.Laurent1.sub {f g : ℂ → ℂ} (hf : LRep1 q f) (hg : LRep1 q g) : LRep1 q (fun s => f s - g s) :=
  congr hq (fun s => by ring) (add hq hf (neg hq hg))

p2m_export "Ws1.Middle.Laurent1" "sub"
private theorem _root_.Ws1.Middle.Laurent1.smul (c : ℂ) {f : ℂ → ℂ} (hf : LRep1 q f) : LRep1 q (fun s => c * f s) :=
  mul hq (const hq c) hf

p2m_export "Ws1.Middle.Laurent1" "smul"
private theorem _root_.Ws1.Middle.Laurent1.pow {f : ℂ → ℂ} (hf : LRep1 q f) (n : ℕ) : LRep1 q (fun s => f s ^ n) := by
  induction n with
  | zero => exact congr hq (fun s => by rw [pow_zero]) (const hq 1)
  | succ n ih => exact congr hq (fun s => by rw [pow_succ]) (mul hq ih hf)

p2m_export "Ws1.Middle.Laurent1" "pow"

theorem sum {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ T, LRep1 q (f i)) :
    LRep1 q (fun s => ∑ i ∈ T, f i s) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact congr hq (fun s => by rw [Finset.sum_empty]) (const hq 0)
  | insert a T ha ih =>
    refine congr hq (fun s => by rw [Finset.sum_insert ha]) (add hq (hf a (Finset.mem_insert_self a T)) ?_)
    exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

private theorem _root_.Ws1.Middle.Laurent1.prod {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ T, LRep1 q (f i)) :
    LRep1 q (fun s => ∏ i ∈ T, f i s) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact congr hq (fun s => by rw [Finset.prod_empty]) (const hq 1)
  | insert a T ha ih =>
    refine congr hq (fun s => by rw [Finset.prod_insert ha]) (mul hq (hf a (Finset.mem_insert_self a T)) ?_)
    exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

p2m_export "Ws1.Middle.Laurent1" "prod"

theorem polyEval (D : Polynomial ℂ) {g : ℂ → ℂ} (hg : LRep1 q g) : LRep1 q (fun s => D.eval (g s)) := by
  refine congr hq (fun s => (Polynomial.eval_eq_sum_range (g s)).symm) ?_
  exact sum hq _ fun i _ => smul hq _ (pow hq hg i)

theorem mvEval₂ (P : MvPolynomial (Fin 2) ℂ) {g₁ g₂ : ℂ → ℂ} (hg₁ : LRep1 q g₁) (hg₂ : LRep1 q g₂) :
    LRep1 q (fun s => MvPolynomial.eval ![g₁ s, g₂ s] P) := by
  induction P using MvPolynomial.induction_on with
  | C a => exact congr hq (fun s => (MvPolynomial.eval_C a).symm) (const hq a)
  | add p r hp hr => exact congr hq (fun s => (map_add _ p r).symm) (add hq hp hr)
  | mul_X p i hp =>
    refine congr hq (fun s => (by rw [map_mul, MvPolynomial.eval_X])) (mul hq hp ?_)
    fin_cases i
    · exact congr hq (fun s => by simp) hg₁
    · exact congr hq (fun s => by simp) hg₂

theorem cx_zpow (c : ℂ) (hc : c ≠ 0) (N : ℤ) : LRep1 q (fun s => (c * (q : ℂ) ^ (-s)) ^ N) := by
  rcases Int.eq_nat_or_neg N with ⟨n, rfl | rfl⟩
  · exact congr hq (fun s => by rw [zpow_natCast]) (pow hq (smul hq c (x hq)) n)
  · refine ⟨Polynomial.C (c⁻¹ ^ n), n, fun s => ?_⟩
    show (c * (q : ℂ) ^ (-s)) ^ (-(n : ℤ)) * ((q : ℂ) ^ (-s)) ^ n = Polynomial.eval ((q : ℂ) ^ (-s)) (Polynomial.C (c⁻¹ ^ n))
    rw [zpow_neg, zpow_natCast, Polynomial.eval_C, mul_pow, mul_inv, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ (x_ne_zero hq s)), mul_one, inv_pow]

theorem cxinv_zpow (c : ℂ) (hc : c ≠ 0) (N : ℤ) : LRep1 q (fun s => (c * ((q : ℂ) ^ (-s))⁻¹) ^ N) := by
  rcases Int.eq_nat_or_neg N with ⟨n, rfl | rfl⟩
  · exact congr hq (fun s => by rw [zpow_natCast]) (pow hq (smul hq c (xinv' hq)) n)
  · refine congr hq (fun s => ?_) (pow hq (smul hq c⁻¹ (x hq)) n)
    rw [zpow_neg, zpow_natCast, ← inv_pow, mul_inv, inv_inv]

theorem q_one_sub' : LRep1 q (fun s => (q : ℂ) ^ (1 - s)) :=
  congr hq (fun s => (q_one_sub hq s).symm) (smul hq _ (x hq))

theorem q_neg_add' (a : ℂ) : LRep1 q (fun s => (q : ℂ) ^ (-(s + a))) :=
  congr hq (fun s => (q_neg_add hq a s).symm) (smul hq _ (x hq))

theorem q_neg_sub' (a : ℂ) : LRep1 q (fun s => (q : ℂ) ^ (-(a - s))) :=
  congr hq (fun s => (q_neg_sub hq a s).symm) (smul hq _ (xinv' hq))

theorem q_natMul_sub' (n : ℕ) (a : ℂ) : LRep1 q (fun s => (q : ℂ) ^ ((n : ℂ) * (a - s))) :=
  congr hq (fun s => (q_natMul_sub hq n a s).symm) (smul hq _ (pow hq (x hq) n))

end Closure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

section Extract

variable {q : ℕ} (hq : 1 < q)
include hq

theorem exists_poly {f : ℂ → ℂ} (hf : LRep1 q f) :
    ∃ (m : Polynomial ℂ) (M : ℕ), ∀ s : ℂ, m.eval ((q : ℂ) ^ (-s)) = ((q : ℂ) ^ (-s)) ^ M * f s := by
  obtain ⟨P, M, h⟩ := hf
  exact ⟨P, M, fun s => by rw [← h s, mul_comm]⟩

theorem exists_poly_zpow {f : ℂ → ℂ} (hf : LRep1 q f) (M : ℕ) :
    ∃ (m : Polynomial ℂ) (k : ℤ), ∀ s : ℂ,
      m.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) = ((q : ℂ) ^ (-s)) ^ M * f s := by
  obtain ⟨P, Mf, h⟩ := hf
  rcases Nat.lt_or_ge M Mf with hlt | hle
  swap
  · refine ⟨P * Polynomial.X ^ (M - Mf), 0, fun s => ?_⟩
    rw [Int.cast_zero, zero_mul, Complex.cpow_zero, mul_one, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, ← h s, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle, mul_comm]
  · refine ⟨P, ((Mf - M : ℕ) : ℤ), fun s => ?_⟩
    rw [Int.cast_natCast, ← qs_pow hq, ← h s]
    have hx := x_ne_zero hq s
    have : ((q : ℂ) ^ (-s)) ^ Mf = ((q : ℂ) ^ (-s)) ^ M * ((q : ℂ) ^ (-s)) ^ (Mf - M) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [this, qs_eq_inv hq s, inv_pow, mul_assoc, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one, mul_comm]

theorem poly_ne_zero {f : ℂ → ℂ} {m : Polynomial ℂ} {M : ℕ}
    (h : ∀ s : ℂ, m.eval ((q : ℂ) ^ (-s)) = ((q : ℂ) ^ (-s)) ^ M * f s) {s₀ : ℂ} (hs₀ : f s₀ ≠ 0) : m ≠ 0 := by
  intro hm
  have := h s₀
  rw [hm, Polynomial.eval_zero] at this
  exact (mul_ne_zero (pow_ne_zero _ (x_ne_zero hq s₀)) hs₀) this.symm

end Extract
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

section Roots

theorem exists_forall_eval_ne_zero_of_norm_lt (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < δ → Q.eval z ≠ 0 := by
  classical
  set S : Finset ℂ := Q.roots.toFinset.filter (fun r => r ≠ 0) with hS
  by_cases hne : S.Nonempty
  · refine ⟨S.inf' hne (fun r => ‖r‖), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro r hr
      exact norm_pos_iff.mpr (Finset.mem_filter.mp hr).2
    · intro z hz0 hz hQz
      have hzS : z ∈ S := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hQz), hz0⟩
      exact (not_lt.mpr (Finset.inf'_le _ hzS)) hz
  · refine ⟨1, one_pos, fun z hz0 _ hQz => hne ⟨z, ?_⟩⟩
    exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hQz), hz0⟩

theorem exists_forall_eval_ne_zero_of_lt_norm (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ B : ℝ, ∀ z : ℂ, B < ‖z‖ → Q.eval z ≠ 0 := by
  classical
  set S : Finset ℂ := Q.roots.toFinset with hS
  by_cases hne : S.Nonempty
  · refine ⟨S.sup' hne (fun r => ‖r‖), fun z hz hQz => ?_⟩
    have hzS : z ∈ S := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hQz)
    exact (not_lt.mpr (Finset.le_sup' (fun r => ‖r‖) hzS)) hz
  · exact ⟨0, fun z _ hQz => hne ⟨z, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hQz)⟩⟩

end Roots
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

section Far

variable {q : ℕ} (hq : 1 < q)
include hq

theorem norm_cpow (s : ℂ) : ‖(q : ℂ) ^ s‖ = (q : ℝ) ^ s.re :=
  Complex.norm_natCast_cpow_of_pos (lt_trans zero_lt_one hq) s

theorem tendsto_rpow_neg : Filter.Tendsto (fun σ : ℝ => (q : ℝ) ^ (-σ)) Filter.atTop (nhds 0) := by
  have hN : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hN
  have h := tendsto_rpow_atTop_of_base_lt_one ((q : ℝ))⁻¹ (by linarith [inv_pos.mpr hN0]) (inv_lt_one_of_one_lt₀ hN)
  refine h.congr fun σ => ?_
  rw [Real.inv_rpow hN0.le, Real.rpow_neg hN0.le]

theorem exists_forall_eval_cmul_q_one_sub_ne_zero (D : Polynomial ℂ) (hD : D ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → D.eval (c * (q : ℂ) ^ (1 - s)) ≠ 0 := by
  obtain ⟨δ, hδ, hDδ⟩ := exists_forall_eval_ne_zero_of_norm_lt D hD
  have hN : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hN
  have hc0 : 0 < ‖c‖ * (q : ℝ) := mul_pos (norm_pos_iff.mpr hc) hN0
  obtain ⟨σ, hσ⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_neg hq).eventually (gt_mem_nhds (div_pos hδ hc0)))
  refine ⟨σ, fun s hs => hDδ _ (mul_ne_zero hc (cpow_ne_zero' hq _)) ?_⟩
  rw [norm_mul, norm_cpow hq, Complex.sub_re, Complex.one_re,
    show (1 : ℝ) - s.re = 1 + (-s.re) by ring, Real.rpow_add hN0, Real.rpow_one]
  calc ‖c‖ * ((q : ℝ) * (q : ℝ) ^ (-s.re)) = (‖c‖ * (q : ℝ)) * (q : ℝ) ^ (-s.re) := by ring
    _ ≤ (‖c‖ * (q : ℝ)) * (q : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)) hc0.le
    _ < (‖c‖ * (q : ℝ)) * (δ / (‖c‖ * (q : ℝ))) := mul_lt_mul_of_pos_left (hσ σ le_rfl) hc0
    _ = δ := by field_simp

theorem exists_forall_eval_cmul_qs_ne_zero (D : Polynomial ℂ) (hD : D ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → D.eval (c * (q : ℂ) ^ s) ≠ 0 := by
  obtain ⟨B, hDB⟩ := exists_forall_eval_ne_zero_of_lt_norm D hD
  have hN : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hN
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hB1 : 0 < (max B 1)⁻¹ * ‖c‖ := mul_pos (inv_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _))) hc0
  obtain ⟨σ, hσ⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_neg hq).eventually (gt_mem_nhds hB1))
  refine ⟨σ, fun s hs => hDB _ ?_⟩
  rw [norm_mul, norm_cpow hq]
  have hpos : 0 < (q : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hN0 _
  have h1 : (q : ℝ) ^ (-s.re) < (max B 1)⁻¹ * ‖c‖ :=
    lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)) (hσ σ le_rfl)

  have h2 : max B 1 < ‖c‖ * ((q : ℝ) ^ (-s.re))⁻¹ := by
    have hm : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [lt_mul_inv_iff₀ hpos]
    calc max B 1 * (q : ℝ) ^ (-s.re) < max B 1 * ((max B 1)⁻¹ * ‖c‖) := mul_lt_mul_of_pos_left h1 hm
      _ = ‖c‖ := by field_simp
  rw [Real.rpow_neg hN0.le, inv_inv] at h2
  exact lt_of_le_of_lt (le_max_left _ _) h2

end Far
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

section Example

variable {q : ℕ} (hq : 1 < q)
include hq

theorem lrep_X (α₁ : ℂ) (hα₁ : α₁ ≠ 0) :
    LRep1 q (fun s => α₁⁻¹ * (q : ℂ) ^ (1 - s)) ∧ ∀ N : ℤ, LRep1 q (fun s => (α₁⁻¹ * (q : ℂ) ^ (1 - s)) ^ N) := by
  have h1 : ∀ s : ℂ, α₁⁻¹ * (q : ℂ) ^ (1 - s) = (α₁⁻¹ * q) * (q : ℂ) ^ (-s) := fun s => by
    rw [q_one_sub hq, mul_assoc]
  refine ⟨congr hq (fun s => (h1 s).symm) (smul hq _ (x hq)), fun N => ?_⟩
  exact congr hq (fun s => by rw [h1]) (cx_zpow hq _ (mul_ne_zero (inv_ne_zero hα₁) (qC_ne_zero hq)) N)

theorem lrep_Y (α₀ ωϖ : ℂ) (hα₀ : α₀ ≠ 0) (hω : ωϖ ≠ 0) :
    LRep1 q (fun s => α₀ * ωϖ⁻¹ * (q : ℂ) ^ s) ∧ ∀ N : ℤ, LRep1 q (fun s => (α₀ * ωϖ⁻¹ * (q : ℂ) ^ s) ^ N) := by
  have h1 : ∀ s : ℂ, α₀ * ωϖ⁻¹ * (q : ℂ) ^ s = (α₀ * ωϖ⁻¹) * ((q : ℂ) ^ (-s))⁻¹ := fun s => by
    rw [qs_eq_inv hq s]
  refine ⟨congr hq (fun s => (h1 s).symm) (smul hq _ (xinv' hq)), fun N => ?_⟩
  exact congr hq (fun s => by rw [h1]) (cxinv_zpow hq _ (mul_ne_zero hα₀ (inv_ne_zero hω)) N)

theorem example_dualNF (α₀ α₁ ωϖ C₀ ε a₁' a₂' : ℂ) (hα₀ : α₀ ≠ 0) (hα₁ : α₁ ≠ 0) (hω : ωϖ ≠ 0)
    (ℓ : ℕ) (E Ed Db₁ Db₂ Dt₁ Dt₂ : Polynomial ℂ) (Pb Pt : MvPolynomial (Fin 2) ℂ) (Nb Nt : ℤ)
    (hDb₁ : Db₁.eval 0 ≠ 0) (hDb₂ : Db₂.eval 0 ≠ 0) (hDt₁ : Dt₁.eval 0 ≠ 0) (hDt₂ : Dt₂.eval 0 ≠ 0) :
    let X : ℂ → ℂ := fun s => α₁⁻¹ * (q : ℂ) ^ (1 - s)
    let Y : ℂ → ℂ := fun s => α₀ * ωϖ⁻¹ * (q : ℂ) ^ s
    let wtN : ℂ → ℂ := fun _ => (1 - ((q : ℂ))⁻¹) * ((q : ℂ))⁻¹
    let wtD : ℂ → ℂ := fun _ => 1 - ((q : ℂ))⁻¹
    let cNum : ℂ → ℂ := fun s => C₀ * ε * (q : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) *
      E.eval (a₁' * (q : ℂ) ^ (-(s + 1 / 2))) * Ed.eval (a₂'⁻¹ * (q : ℂ) ^ (-(1 / 2 - s)))
    let Den : ℂ → ℂ := fun s => (Db₁.eval (X s) * Db₂.eval (Y s)) * (Dt₁.eval (X s) * Dt₂.eval (Y s)) * wtD s
    let Num : ℂ → ℂ := fun s => cNum s *
      (X s ^ Nb * Y s ^ Nb * MvPolynomial.eval ![X s, Y s] Pb * (Dt₁.eval (X s) * Dt₂.eval (Y s)) * wtD s +
        wtN s * (X s ^ Nt * Y s ^ Nt * MvPolynomial.eval ![X s, Y s] Pt) * (Db₁.eval (X s) * Db₂.eval (Y s)))
    ∃ (m₁ m₂ : Polynomial ℂ) (k : ℤ) (M : ℕ), m₂ ≠ 0 ∧
      (∀ s : ℂ, m₂.eval ((q : ℂ) ^ (-s)) = ((q : ℂ) ^ (-s)) ^ M * Den s) ∧
      (∀ s : ℂ, m₁.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) = ((q : ℂ) ^ (-s)) ^ M * Num s) := by
  intro X Y wtN wtD cNum Den Num
  obtain ⟨hX, hXz⟩ := lrep_X hq α₁ hα₁
  obtain ⟨hY, hYz⟩ := lrep_Y hq α₀ ωϖ hα₀ hω
  have hwtN : LRep1 q wtN := const hq _
  have hwtD : LRep1 q wtD := const hq _
  have hcNum : LRep1 q cNum := by
    refine mul hq (mul hq (mul hq (const hq _) (q_natMul_sub' hq ℓ _)) (polyEval hq E ?_)) (polyEval hq Ed ?_)
    · exact smul hq _ (q_neg_add' hq _)
    · exact smul hq _ (q_neg_sub' hq _)
  have hDen : LRep1 q Den :=
    mul hq (mul hq (mul hq (polyEval hq _ hX) (polyEval hq _ hY)) (mul hq (polyEval hq _ hX) (polyEval hq _ hY))) hwtD
  have hNum : LRep1 q Num := by
    refine mul hq hcNum (add hq ?_ ?_)
    · exact mul hq (mul hq (mul hq (mul hq (hXz Nb) (hYz Nb)) (mvEval₂ hq Pb hX hY))
        (mul hq (polyEval hq _ hX) (polyEval hq _ hY))) hwtD
    · exact mul hq (mul hq hwtN (mul hq (mul hq (hXz Nt) (hYz Nt)) (mvEval₂ hq Pt hX hY)))
        (mul hq (polyEval hq _ hX) (polyEval hq _ hY))
  obtain ⟨m₂, M, hm₂⟩ := exists_poly hq hDen
  obtain ⟨m₁, k, hm₁⟩ := exists_poly_zpow hq hNum M

  have hne : ∀ D : Polynomial ℂ, D.eval 0 ≠ 0 → D ≠ 0 := fun D hD h => hD (by rw [h, Polynomial.eval_zero])
  obtain ⟨σ₁, hσ₁⟩ := exists_forall_eval_cmul_q_one_sub_ne_zero hq Db₁ (hne _ hDb₁) α₁⁻¹ (inv_ne_zero hα₁)
  obtain ⟨σ₂, hσ₂⟩ := exists_forall_eval_cmul_qs_ne_zero hq Db₂ (hne _ hDb₂) (α₀ * ωϖ⁻¹) (mul_ne_zero hα₀ (inv_ne_zero hω))
  obtain ⟨σ₃, hσ₃⟩ := exists_forall_eval_cmul_q_one_sub_ne_zero hq Dt₁ (hne _ hDt₁) α₁⁻¹ (inv_ne_zero hα₁)
  obtain ⟨σ₄, hσ₄⟩ := exists_forall_eval_cmul_qs_ne_zero hq Dt₂ (hne _ hDt₂) (α₀ * ωϖ⁻¹) (mul_ne_zero hα₀ (inv_ne_zero hω))
  set s₀ : ℂ := ((max (max σ₁ σ₂) (max σ₃ σ₄) + 1 : ℝ) : ℂ) with hs₀
  have hre : s₀.re = max (max σ₁ σ₂) (max σ₃ σ₄) + 1 := by rw [hs₀, Complex.ofReal_re]
  have h1 : σ₁ < s₀.re := by rw [hre]; linarith [le_max_left σ₁ σ₂, le_max_left (max σ₁ σ₂) (max σ₃ σ₄)]
  have h2 : σ₂ < s₀.re := by rw [hre]; linarith [le_max_right σ₁ σ₂, le_max_left (max σ₁ σ₂) (max σ₃ σ₄)]
  have h3 : σ₃ < s₀.re := by rw [hre]; linarith [le_max_left σ₃ σ₄, le_max_right (max σ₁ σ₂) (max σ₃ σ₄)]
  have h4 : σ₄ < s₀.re := by rw [hre]; linarith [le_max_right σ₃ σ₄, le_max_right (max σ₁ σ₂) (max σ₃ σ₄)]
  have hwt : (1 : ℂ) - ((q : ℂ))⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    have : ((q : ℂ))⁻¹ = ((q : ℝ)⁻¹ : ℝ) := by push_cast; rfl
    have hq1 : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)
    intro h
    rw [this] at h
    exact hq1.ne (by exact_mod_cast h)
  have hDen0 : Den s₀ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hσ₁ s₀ h1) (hσ₂ s₀ h2)) (mul_ne_zero (hσ₃ s₀ h3) (hσ₄ s₀ h4))) hwt
  exact ⟨m₁, m₂, k, M, poly_ne_zero hq hm₂ hDen0, hm₂, hm₁⟩

end Example
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

end Ws1.Middle.Laurent1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

namespace TransportKit

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem modulus_units_ne_zero (a : (p.adicCompletion ℚ)ˣ) :
    ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ p, Complex.ofReal_ne_zero, coe_nnnorm, norm_ne_zero_iff]
  exact a.ne_zero

theorem twist_integrand (χ χt : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χt a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (c : ℂ) (a : (p.adicCompletion ℚ)ˣ) (s : ℂ) :
    c * ((χt a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ)) ^ (s - 1) =
      c * ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ)) ^ (s + t - 1) := by
  rw [hχt a, show s + t - 1 = t + (s - 1) by ring, Complex.cpow_add _ _ (modulus_units_ne_zero p a)]
  ring

theorem twist_inv (χ χt : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χt a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (a : (p.adicCompletion ℚ)ˣ) :
    ((χt⁻¹ a : ℂˣ) : ℂ) = ((χ⁻¹ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-t)) := by
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hχt a,
    mul_inv, Complex.cpow_neg]

variable [MeasurableSpace (p.adicCompletion ℚ)ˣ] [MeasurableSpace (p.adicCompletion ℚ)]

theorem localZeta30_twist (μ : Measure (p.adicCompletion ℚ)ˣ) (W : LocalGL3 p → ℂ)
    (χ χt : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χt a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (s : ℂ) (g : LocalGL3 p) :
    localZeta30 p μ W χt s g = localZeta30 p μ W χ (s + t) g := by
  unfold localZeta30
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  exact twist_integrand p χ χt t hχt _ a s

theorem isLocalZeta30ConvergentAbove_twist (μ : Measure (p.adicCompletion ℚ)ˣ) (W : LocalGL3 p → ℂ)
    (χ χt : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χt a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (g : LocalGL3 p) (σ : ℝ) (h : IsLocalZeta30ConvergentAbove p μ W χ g σ) :
    IsLocalZeta30ConvergentAbove p μ W χt g (σ - t.re) := by
  intro s hs
  have hs' : σ < (s + t).re := by rw [Complex.add_re]; linarith
  refine (h (s + t) hs').congr (Filter.Eventually.of_forall fun a => ?_)
  exact (twist_integrand p χ χt t hχt _ a s).symm

theorem localZeta31_twist (μ : Measure (p.adicCompletion ℚ)ˣ) (ν : Measure (p.adicCompletion ℚ))
    (W : LocalGL3 p → ℂ) (χ χt : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χt a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (s : ℂ) (g : LocalGL3 p) :
    localZeta31 p μ ν W χt s g = localZeta31 p μ ν W χ (s + t) g := by
  unfold localZeta31
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  exact twist_integrand p χ χt t hχt _ a s

theorem isLocalZeta31ConvergentAbove_twist (μ : Measure (p.adicCompletion ℚ)ˣ) (ν : Measure (p.adicCompletion ℚ))
    (W : LocalGL3 p → ℂ) (χ χt : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χt a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (g : LocalGL3 p) (σ : ℝ) (h : IsLocalZeta31ConvergentAbove p μ ν W χ g σ) :
    IsLocalZeta31ConvergentAbove p μ ν W χt g (σ - t.re) := by
  intro s hs
  have hs' : σ < (s + t).re := by rw [Complex.add_re]; linarith
  refine (h (s + t) hs').congr (Filter.Eventually.of_forall fun q => ?_)
  exact (twist_integrand p χ χt t hχt _ q.1 s).symm

theorem localZetaDual31_twist (μ : Measure (p.adicCompletion ℚ)ˣ) (ν : Measure (p.adicCompletion ℚ))
    (W : LocalGL3 p → ℂ) (χ χt : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χt a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (s : ℂ) (g : LocalGL3 p) :
    localZetaDual31 p μ ν W χt (1 - s) g = localZetaDual31 p μ ν W χ (1 - (s + t)) g := by
  unfold localZetaDual31
  rw [localZeta31_twist p μ ν (dualWhittakerFn3 W) χ⁻¹ χt⁻¹ (-t) (twist_inv p χ χt t hχt)]
  congr 1; ring

theorem isLocalZeta31ConvergentAbove_dual_twist (μ : Measure (p.adicCompletion ℚ)ˣ) (ν : Measure (p.adicCompletion ℚ))
    (W : LocalGL3 p → ℂ) (χ χt : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χt a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (g : LocalGL3 p) (σ : ℝ) (h : IsLocalZeta31ConvergentAbove p μ ν (dualWhittakerFn3 W) χ⁻¹ g σ) :
    IsLocalZeta31ConvergentAbove p μ ν (dualWhittakerFn3 W) χt⁻¹ g (σ + t.re) := by
  have := isLocalZeta31ConvergentAbove_twist p μ ν (dualWhittakerFn3 W) χ⁻¹ χt⁻¹ (-t) (twist_inv p χ χt t hχt) g σ h
  simpa using this

end TransportKit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

namespace TransportKit

open Polynomial

theorem exists_forall_eval_cpow_ne_zero (N : ℕ) (hN : 1 < N) (E : Polynomial ℂ) (hE : E ≠ 0) :
    ∃ σE : ℝ, ∀ s : ℂ, σE < s.re → E.eval ((N : ℂ) ^ (-s)) ≠ 0 := by
  have hNpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN

  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ E.roots, z ≠ 0 → r ≤ ‖z‖ := by
    classical
    let S := (E.roots.toFinset.filter (· ≠ 0)).image (fun z : ℂ => ‖z‖)
    by_cases hS : S.Nonempty
    · refine ⟨S.min' hS, ?_, fun z hz hz0 => S.min'_le _ ?_⟩
      · obtain ⟨z, hz⟩ := hS
        have hpos : ∀ x ∈ S, 0 < x := by
          intro x hx
          simp only [S, Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset] at hx
          obtain ⟨w, ⟨-, hw0⟩, rfl⟩ := hx
          exact norm_pos_iff.mpr hw0
        exact (Finset.lt_min'_iff _ _).mpr hpos
      · simp only [S, Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset]
        exact ⟨z, ⟨hz, hz0⟩, rfl⟩
    · refine ⟨1, one_pos, fun z hz hz0 => ?_⟩
      exact absurd ⟨‖z‖, by simp only [S, Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset]; exact ⟨z, ⟨hz, hz0⟩, rfl⟩⟩ hS

  refine ⟨-Real.logb N r, fun s hs h0 => ?_⟩
  have hroot : (N : ℂ) ^ (-s) ∈ E.roots := (Polynomial.mem_roots hE).mpr h0
  have hne : (N : ℂ) ^ (-s) ≠ 0 := by
    intro h; rw [Complex.cpow_eq_zero_iff] at h; exact_mod_cast (show (N : ℕ) ≠ 0 by omega) |> fun hh => hh (by exact_mod_cast h.1)
  have hle := hr _ hroot hne
  have hnorm : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos]; simp
  rw [hnorm] at hle

  have hlt : (N : ℝ) ^ (-s.re) < (N : ℝ) ^ (Real.logb N r) :=
    (Real.rpow_lt_rpow_left_iff hN1).mpr (by linarith)
  rw [Real.rpow_logb (by positivity) hN1.ne' hr0] at hlt
  linarith

end TransportKit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

namespace TransportKit

open Polynomial

theorem one_lt_q (p : HeightOneSpectrum (𝓞 ℚ)) : 1 < Ideal.absNorm p.asIdeal := by
  refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot, ?_⟩
  exact Ideal.absNorm_eq_one_iff.not.mpr (Ideal.IsPrime.ne_top p.isPrime)

theorem qC_ne_zero (p : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
  have := one_lt_q p; exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)

theorem cpow_ne_zero' (p : HeightOneSpectrum (𝓞 ℚ)) (z : ℂ) : (Ideal.absNorm p.asIdeal : ℂ) ^ z ≠ 0 := by
  intro h; rw [Complex.cpow_eq_zero_iff] at h; exact qC_ne_zero p h.1

theorem comp_CX_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) {c : ℂ} (hc : c ≠ 0) : P.comp (C c * X) ≠ 0 := by
  intro h
  rw [Polynomial.comp_eq_zero_iff] at h
  rcases h with h | ⟨-, h⟩
  · exact hP h
  · have := congrArg (fun q : Polynomial ℂ => q.coeff 1) h
    simp at this
    exact hc this

theorem fold_twist (p : HeightOneSpectrum (𝓞 ℚ)) [MeasurableSpace (p.adicCompletion ℚ)ˣ] [MeasurableSpace (p.adicCompletion ℚ)]
    (μ : Measure (p.adicCompletion ℚ)ˣ) (ν : Measure (p.adicCompletion ℚ))
    (E Ed : Polynomial ℂ) (hE : E ≠ 0) (ε : ℂ) (ℓ : ℕ) (t : ℂ)
    (W' : LocalGL3 p → ℂ) (χ χt : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χt a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (g : LocalGL3 p)
    (hpkg : ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove p μ W' χ g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p μ W' χ s g = (E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove p μ ν (dualWhittakerFn3 W') χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p μ ν W' χ (1 - s) g =
            (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)) :
    ∃ (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
      IsLocalZeta30ConvergentAbove p μ W' χt g σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 p μ W' χt s g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)) ∧
      IsLocalZeta31ConvergentAbove p μ ν (dualWhittakerFn3 W') χt⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
      (∀ s : ℂ, σ₁ < (1 - s).re →
        localZetaDual31 p μ ν W' χt (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s) *
            (ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - (s + t))) *
              E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(s + t))) *
              (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - (s + t)))))⁻¹)) := by
  obtain ⟨P, σ₀, σ₁, ⟨Q, R, m, hR, hPR⟩, hc30, he30, hc31, he31⟩ := hpkg
  set qC : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hqC
  have hq : 1 < Ideal.absNorm p.asIdeal := one_lt_q p
  have hqC0 : qC ≠ 0 := qC_ne_zero p
  set c : ℂ := qC ^ (-t) with hc
  have hc0 : c ≠ 0 := cpow_ne_zero' p _

  have hsub : ∀ s : ℂ, qC ^ (-(s + t)) = c * qC ^ (-s) := by
    intro s; rw [hc, ← Complex.cpow_add _ _ hqC0]; congr 1; ring
  have hevc : ∀ (F : Polynomial ℂ) (s : ℂ), (F.comp (C c * X)).eval (qC ^ (-s)) = F.eval (qC ^ (-(s + t))) := by
    intro F s; rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hsub]
  obtain ⟨σE, hσE⟩ := exists_forall_eval_cpow_ne_zero (Ideal.absNorm p.asIdeal) hq E hE
  refine ⟨Polynomial.C (qC ^ ((m : ℂ) * t)) * Q.comp (C c * X), (E * R).comp (C c * X), (m : ℤ),
    max (σ₀ - t.re) (σE - t.re), σ₁ + t.re, comp_CX_ne_zero (mul_ne_zero hE hR) hc0, ?_, ?_, ?_, ?_⟩
  · exact fun s hs => isLocalZeta30ConvergentAbove_twist p μ W' χ χt t hχt g σ₀ hc30 s
      (lt_of_le_of_lt (le_max_left _ _) hs)
  · intro s hs
    have h1 : σ₀ < (s + t).re := by rw [Complex.add_re]; linarith [lt_of_le_of_lt (le_max_left _ _) hs]
    have h2 : σE < (s + t).re := by rw [Complex.add_re]; linarith [lt_of_le_of_lt (le_max_right _ _) hs]
    have hE0 : E.eval (qC ^ (-(s + t))) ≠ 0 := by rw [hqC]; exact hσE (s + t) h2
    rw [localZeta30_twist p μ W' χ χt t hχt s g, he30 (s + t) h1]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, hevc]
    have hPR' := hPR (s + t)
    have hpow : qC ^ ((m : ℂ) * (s + t)) = qC ^ ((m : ℂ) * t) * qC ^ (((m : ℤ) : ℂ) * s) := by
      rw [← Complex.cpow_add _ _ hqC0]; congr 1; push_cast; ring
    rw [hpow] at hPR'
    rw [show (E.eval (qC ^ (-(s + t))))⁻¹ * P (s + t) * (E.eval (qC ^ (-(s + t))) * R.eval (qC ^ (-(s + t)))) =
        (P (s + t) * R.eval (qC ^ (-(s + t)))) * ((E.eval (qC ^ (-(s + t))))⁻¹ * E.eval (qC ^ (-(s + t)))) by ring,
      inv_mul_cancel₀ hE0, mul_one, hPR']
    ring
  · exact isLocalZeta31ConvergentAbove_dual_twist p μ ν W' χ χt t hχt _ σ₁ hc31
  · intro s hs
    have h1 : σ₁ < (1 - (s + t)).re := by
      rw [Complex.sub_re, Complex.add_re, Complex.one_re]; rw [Complex.sub_re, Complex.one_re] at hs; linarith
    rw [localZetaDual31_twist p μ ν W' χ χt t hχt s g, he31 (s + t) h1]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, hevc]
    have hPR' := hPR (s + t)
    have hpow : qC ^ ((m : ℂ) * (s + t)) = qC ^ ((m : ℂ) * t) * qC ^ (((m : ℤ) : ℂ) * s) := by
      rw [← Complex.cpow_add _ _ hqC0]; congr 1; push_cast; ring
    rw [hpow] at hPR'
    linear_combination (ε * qC ^ ((ℓ : ℂ) * (1 / 2 - (s + t))) * (Ed.eval (qC ^ (-(1 - (s + t)))))⁻¹ *
      E.eval (qC ^ (-(s + t)))) * hPR'

end TransportKit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

namespace TransportKit

theorem gl3CyclicSubspace_le_of_mem {p : HeightOneSpectrum (𝓞 ℚ)} {W V : LocalGL3 p → ℂ}
    (hV : V ∈ gl3CyclicSubspace W) : gl3CyclicSubspace V ≤ gl3CyclicSubspace W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h₀, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h₀ hV

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem transport_primal (p : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 p → ℂ) (E Ed : Polynomial ℂ) (hE : E ≠ 0) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 p,
      (letI := localBorel ℚ p
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W 1 s g =
            (E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (selfDualHaarAt ℚ p) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (W'' : LocalGL3 p → ℂ) (hW''mem : W'' ∈ gl3CyclicSubspace W)
    (hW''law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W'')
    (hW''sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W'' (g * k) = W'' g)
    (t : ℂ) (χt : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ, ((χt a : ℂˣ) : ℂ) = (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (g : LocalGL3 p) :
    letI := localBorel ℚ p
    ∃ (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
      IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
        W'' χt g σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) W'' χt s g *
            Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        (dualWhittakerFn3 W'') χt⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
      (∀ s : ℂ, σ₁ < (1 - s).re →
        (Ideal.absNorm p.asIdeal : ℂ) ^ (0 : ℤ) *
              (((selfDualHaarAt ℚ p).real {x : p.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 *
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (dualWhittakerFn3 W'') χt⁻¹
              (1 - s) (weylPrime3 * transposeInv3 g) *
            Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s) *
            (ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - (s + t))) *
              E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(s + t))) *
              (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - (s + t)))))⁻¹)) := by
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
    set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
      with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact (NNReal.rpow_pos
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
    have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
    rw [hdef]
    exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

  set ψ := NumberField.StandardAddChar.psiLocal ℚ p with hψdef
  have hlevel : addCharLevel ψ = 0 := LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p
  have hψk : ∃ k : ℤ, ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → ψ x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← WithZero.exp_zero]
    exact hx
  obtain ⟨hψn, hψn'⟩ := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p ψ hψk
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rw [hlevel] at hψn hψn'

  have pkg := LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
    p W E Ed ε ℓ h31
  have hle := gl3CyclicSubspace_le_of_mem hW''mem
  have hχt' : ∀ a : (p.adicCompletion ℚ)ˣ, ((χt a : ℂˣ) : ℂ) =
      (((1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t) := by
    intro a; rw [hχt a]; simp
  have key := LanglandsTunnell.CubicInduction.exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
    p ψ 0 hψn (by simpa using hψn') W'' hW''law hW''sm χt
    (fun s => ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - (s + t))) *
      E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(s + t))) *
      (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - (s + t)))))⁻¹) g
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
    (fun W' hW' => fold_twist p _ _ E Ed hE ε ℓ t W' 1 χt hχt' g (pkg W' (hle hW') g))
  simpa only [Int.cast_zero] using key

end TransportKit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

namespace TransportKit

section DualAlgebra

open scoped Matrix

variable {A : Type*} [CommRing A]

private theorem _root_.TransportKit.transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

p2m_export "TransportKit" "transposeInv3_coe"
private theorem _root_.TransportKit.transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

p2m_export "TransportKit" "transposeInv3_mul"
private theorem _root_.TransportKit.transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

p2m_export "TransportKit" "transposeInv3_transposeInv3"
theorem transposeInv3_longWeyl3 : transposeInv3 (longWeyl3 : GL (Fin 3) A) = longWeyl3 := by
  refine Units.ext ?_
  change (((longWeyl3 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  change ((longWeyl3 : GL (Fin 3) A).inv)ᵀ = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longWeyl3]

theorem longWeyl3_mul_longWeyl3 : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem weylPrime3_transposeInv3_weylPrime3_transposeInv3 (g : GL (Fin 3) A) :
    weylPrime3 * transposeInv3 (weylPrime3 * transposeInv3 g) = g := by
  rw [transposeInv3_mul, transposeInv3_weylPrime3, transposeInv3_transposeInv3, ← mul_assoc, weylPrime3_mul_self,
    one_mul]

theorem dualWhittakerFn3_dualWhittakerFn3 {R : Type*} (Φ : GL (Fin 3) A → R) :
    dualWhittakerFn3 (dualWhittakerFn3 Φ) = Φ := by
  funext g
  simp only [dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_longWeyl3, transposeInv3_transposeInv3,
    ← mul_assoc, longWeyl3_mul_longWeyl3, one_mul]

end DualAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem transport_dual (p : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 p → ℂ) (E Ed : Polynomial ℂ) (hE : E ≠ 0) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 p,
      (letI := localBorel ℚ p
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W 1 s g =
            (E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (selfDualHaarAt ℚ p) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (V : LocalGL3 p → ℂ) (hVmem : dualWhittakerFn3 V ∈ gl3CyclicSubspace W)
    (t : ℂ) (χt : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχt : ∀ a : (p.adicCompletion ℚ)ˣ, ((χt a : ℂˣ) : ℂ) = (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (g : LocalGL3 p) :
    letI := localBorel ℚ p
    ∃ (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
      IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        (dualWhittakerFn3 V) χt (weylPrime3 * transposeInv3 g) σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (dualWhittakerFn3 V) χt s
            (weylPrime3 * transposeInv3 g) * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)) ∧
      IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
        V χt⁻¹ g σ₁ ∧
      (∀ s : ℂ, σ₁ < (1 - s).re →
        localZeta31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) V χt⁻¹
            (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s) *
            (ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - (s + t))) *
              E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(s + t))) *
              (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - (s + t)))))⁻¹)) := by
  have pkg := LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
    p W E Ed ε ℓ h31 (dualWhittakerFn3 V) hVmem (weylPrime3 * transposeInv3 g)
  have hχt' : ∀ a : (p.adicCompletion ℚ)ˣ, ((χt a : ℂˣ) : ℂ) =
      (((1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t) := by
    intro a; rw [hχt a]; simp
  obtain ⟨Q₁, Q₂, k, σ₀, σ₁, hQ₂, hc30, he30, hc31, he31⟩ :=
    fold_twist p _ _ E Ed hE ε ℓ t (dualWhittakerFn3 V) 1 χt hχt' (weylPrime3 * transposeInv3 g) pkg
  refine ⟨Q₁, Q₂, k, σ₀, σ₁, hQ₂, hc30, he30, ?_, ?_⟩
  · simpa only [dualWhittakerFn3_dualWhittakerFn3, weylPrime3_transposeInv3_weylPrime3_transposeInv3] using hc31
  · intro s hs
    have := he31 s hs
    unfold localZetaDual31 at this
    simpa only [dualWhittakerFn3_dualWhittakerFn3, weylPrime3_transposeInv3_weylPrime3_transposeInv3] using this

end TransportKit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace Ws1
namespace Middle
namespace Eval

theorem natCast_cpow_neg_ne_zero (N : ℕ) (hN : 1 < N) (s : ℂ) : (N : ℂ) ^ (-s) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  left
  exact_mod_cast (show N ≠ 0 by omega)

theorem ofReal_rpow_natCast (N : ℕ) (u : ℝ) :
    (((N : ℝ) ^ u : ℝ) : ℂ) = (N : ℂ) ^ (u : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg N)]
  norm_cast

theorem natCast_cpow_neg_ofReal (N : ℕ) (t : ℝ) :
    (N : ℂ) ^ (-(t : ℂ)) = (((N : ℝ) ^ (-t) : ℝ) : ℂ) := by
  rw [ofReal_rpow_natCast]
  norm_cast

theorem norm_natCast_cpow_neg (N : ℕ) (hN : 1 < N) (s : ℂ) :
    ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem infinite_image_cpow_neg_halfPlane (N : ℕ) (hN : 1 < N) (σ : ℝ) :
    Set.Infinite ((fun s : ℂ => (N : ℂ) ^ (-s)) '' {s : ℂ | σ < s.re}) := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinj : Function.Injective (fun t : ℝ => (((N : ℝ) ^ (-t) : ℝ) : ℂ)) := by
    intro a b hab
    dsimp only at hab
    have h1 : (N : ℝ) ^ (-a) = (N : ℝ) ^ (-b) := by exact_mod_cast hab
    have h2 := (Real.strictMono_rpow_of_base_gt_one hN').injective h1
    linarith
  have hsub : ((fun t : ℝ => (((N : ℝ) ^ (-t) : ℝ) : ℂ)) '' Set.Ioi σ) ⊆
      ((fun s : ℂ => (N : ℂ) ^ (-s)) '' {s : ℂ | σ < s.re}) := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨(t : ℂ), by simpa using ht, ?_⟩
    simp only [natCast_cpow_neg_ofReal]
  exact ((Set.Ioi_infinite σ).image hinj.injOn).mono hsub

theorem infinite_setOf_of_forall_lt_re (N : ℕ) (hN : 1 < N) (σ : ℝ) (p : ℂ → Prop)
    (h : ∀ s : ℂ, σ < s.re → p ((N : ℂ) ^ (-s))) : Set.Infinite {x : ℂ | p x} :=
  (infinite_image_cpow_neg_halfPlane N hN σ).mono (by rintro _ ⟨s, hs, rfl⟩; exact h s hs)

theorem polynomial_eq_of_forall_lt_re_eval_eq (N : ℕ) (hN : 1 < N) (σ : ℝ) (p q : Polynomial ℂ)
    (h : ∀ s : ℂ, σ < s.re → p.eval ((N : ℂ) ^ (-s)) = q.eval ((N : ℂ) ^ (-s))) : p = q :=
  Polynomial.eq_of_infinite_eval_eq p q
    (infinite_setOf_of_forall_lt_re N hN σ (fun x => Polynomial.eval x p = Polynomial.eval x q) h)

theorem polynomial_eq_of_forall_lt_re_eval_sub_one_eq (N : ℕ) (hN : 1 < N) (σ : ℝ) (p q : Polynomial ℂ)
    (h : ∀ s : ℂ, σ < s.re → p.eval ((N : ℂ) ^ (-(s - 1))) = q.eval ((N : ℂ) ^ (-(s - 1)))) : p = q := by
  refine polynomial_eq_of_forall_lt_re_eval_eq N hN (σ - 1) p q fun s hs => ?_
  have := h (s + 1) (by simp; linarith)
  simpa only [add_sub_cancel_right] using this

theorem polynomial_mul_eq_of_forall_lt_re (N : ℕ) (hN : 1 < N) (σ : ℝ) (f : ℂ → ℂ)
    (Q₁ Q₂ M D : Polynomial ℂ)
    (h₁ : ∀ s : ℂ, σ < s.re → f s * Q₂.eval ((N : ℂ) ^ (-s)) = Q₁.eval ((N : ℂ) ^ (-s)))
    (h₂ : ∀ s : ℂ, σ < s.re → f s * D.eval ((N : ℂ) ^ (-s)) = M.eval ((N : ℂ) ^ (-s))) :
    Q₁ * D = M * Q₂ := by
  refine polynomial_eq_of_forall_lt_re_eval_eq N hN σ _ _ fun s hs => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_mul, ← h₁ s hs, ← h₂ s hs]
  ring

theorem exists_forall_lt_re_norm_cpow_neg_sub_one_lt (N : ℕ) (hN : 1 < N) {r : ℝ} (hr : 0 < r) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ‖(N : ℂ) ^ (-(s - 1))‖ < r := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((N : ℝ)⁻¹) ^ n < r := exists_pow_lt_of_lt_one hr (inv_lt_one_of_one_lt₀ hN')
  refine ⟨n + 1, fun s hs => ?_⟩
  have e : -(s - 1) = -((s - 1 : ℂ)) := rfl
  rw [show (N : ℂ) ^ (-(s - 1)) = (N : ℂ) ^ (-((s - 1 : ℂ))) from rfl, norm_natCast_cpow_neg N hN]
  calc (N : ℝ) ^ (-(s - 1).re) < (N : ℝ) ^ (-(n : ℝ)) :=
        (Real.rpow_lt_rpow_left_iff hN').2 (by simp; linarith)
    _ = ((N : ℝ)⁻¹) ^ n := by rw [Real.rpow_neg hNpos.le, Real.rpow_natCast, inv_pow]
    _ < r := hn

theorem hasSum_int_of_support (a : ℤ → ℂ) (N₁ : ℤ) (hsupp : ∀ n : ℤ, n < N₁ → a n = 0)
    (X : ℂ) (hX : X ≠ 0) (T : ℂ) (hT : HasSum (fun m : ℕ => a (N₁ + m) * X ^ m) T) :
    HasSum (fun n : ℤ => a n * X ^ n) (X ^ N₁ * T) := by
  have hinj : Function.Injective (fun m : ℕ => N₁ + (m : ℤ)) := fun a b h => by
    simpa using h
  rw [← hinj.hasSum_iff]
  · have : (fun n : ℤ => a n * X ^ n) ∘ (fun m : ℕ => N₁ + (m : ℤ)) =
        fun m : ℕ => X ^ N₁ * (a (N₁ + m) * X ^ m) := by
      funext m
      simp only [Function.comp_apply, zpow_add₀ hX, zpow_natCast]
      ring
    rw [this]
    exact hT.mul_left _
  · intro n hn
    have : n < N₁ := by
      by_contra h
      exact hn ⟨(n - N₁).toNat, by simp [Int.toNat_of_nonneg (sub_nonneg.2 (not_lt.1 h))]⟩
    simp [hsupp n this]

theorem exists_hasSum_row_and_mul_eval_eq (A : ℤ × ℤ → ℂ) (N₁ : ℤ)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (D₁ : Polynomial ℂ) (q : ℕ → Polynomial ℂ) (r : ℝ)
    (hrow : ∀ (j : ℕ) (X : ℂ), ‖X‖ < r →
      Summable (fun m₁ : ℕ => ‖A (N₁ + (m₁ : ℤ), N₁ + (j : ℤ)) * X ^ m₁‖) ∧
      (∑' m₁ : ℕ, A (N₁ + (m₁ : ℤ), N₁ + (j : ℤ)) * X ^ m₁) * D₁.eval X = (q j).eval X)
    (k : ℤ) (hk : N₁ ≤ k) (X : ℂ) (hX : ‖X‖ < r) (hX0 : X ≠ 0) :
    ∃ S : ℂ, HasSum (fun n : ℤ => A (n, k) * X ^ n) S ∧ S * D₁.eval X = X ^ N₁ * (q (k - N₁).toNat).eval X := by
  obtain ⟨hsum, hq⟩ := hrow (k - N₁).toNat X hX
  have hk' : N₁ + ((k - N₁).toNat : ℤ) = k := by
    rw [Int.toNat_of_nonneg (sub_nonneg.2 hk)]; ring
  rw [hk'] at hsum hq
  refine ⟨X ^ N₁ * ∑' m₁ : ℕ, A (N₁ + (m₁ : ℤ), k) * X ^ m₁, ?_, ?_⟩
  · exact hasSum_int_of_support (fun n => A (n, k)) N₁ (fun n hn => hsupp (n, k) (Or.inl hn)) X hX0 _
      hsum.of_norm.hasSum
  · rw [mul_assoc, hq]

section Mat

variable {K : Type*} [Field K]

theorem diagZ_eq_diagUnitGL2 (π : K) (hπ : π ≠ 0) (n : ℤ) :
    diagZ π hπ n = diagUnitGL2 (Units.mk0 π hπ ^ n) := by
  refine Units.ext ?_
  show (!![π ^ n, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) = ((diagUnitGL2 (Units.mk0 π hπ ^ n) : GL (Fin 2) K) : Matrix _ _ _)
  rw [coe_diagUnitGL2, Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem scalarPi_comm (π : K) (hπ : π ≠ 0) (g : GL (Fin 2) K) :
    scalarPi π hπ * g = g * scalarPi π hπ := by
  refine Units.ext ?_
  have h : ((scalarPi π hπ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = π • (1 : Matrix (Fin 2) (Fin 2) K) := by
    show (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) K) = π • 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [Units.val_mul, Units.val_mul, h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem scalarPi_zpow_comm (π : K) (hπ : π ≠ 0) (n : ℤ) (g : GL (Fin 2) K) :
    scalarPi π hπ ^ n * g = g * scalarPi π hπ ^ n :=
  ((show Commute (scalarPi π hπ) g from scalarPi_comm π hπ g).zpow_left n).eq

theorem iotaGL_diagZ_mul_scalarPi_zpow (π : K) (hπ : π ≠ 0) (n k : ℤ) :
    (iotaGL (diagZ π hπ n * scalarPi π hπ ^ k) : GL (Fin 3) K) =
      iotaGL (scalarPi π hπ ^ k * diagUnitGL2 (Units.mk0 π hπ ^ n)) := by
  rw [diagZ_eq_diagUnitGL2, scalarPi_zpow_comm]

end Mat
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

theorem natCast_cpow_neg_int_mul (N : ℕ) (n : ℤ) (z : ℂ) :
    (N : ℂ) ^ (-((n : ℂ) * z)) = ((N : ℂ) ^ (-z)) ^ n := by
  rw [show -((n : ℂ) * z) = (n : ℂ) * (-z) by ring, Complex.cpow_int_mul]

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem localZeta30_iotaGL_scalarPi_zpow_mul_eval_eq
    (Φ : LocalGL3 v → ℂ)
    (hΦK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, Φ (g * iotaGL k) = Φ g)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (N₁ : ℤ) (D₁ : Polynomial ℂ) (q : ℕ → Polynomial ℂ) (r : ℝ)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) →
      Φ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1))) = 0)
    (hrow : ∀ (j : ℕ) (X : ℂ), ‖X‖ < r →
      Summable (fun m₁ : ℕ =>
        ‖Φ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (j : ℤ)) * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (m₁ : ℤ))))) * X ^ m₁‖) ∧
      (∑' m₁ : ℕ, Φ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (j : ℤ)) * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (m₁ : ℤ))))) * X ^ m₁) *
          D₁.eval X = (q j).eval X)
    (k : ℤ) (hk : N₁ ≤ k) (σ₀ : ℝ)
    (hconv : letI := localBorel ℚ v
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) Φ 1 (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) σ₀)
    (s : ℂ) (hs : σ₀ < s.re) (hX : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))‖ < r) :
    letI := localBorel ℚ v
    localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) Φ 1 s (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) * D₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) =
      (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}).toReal : ℂ) *
        (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ N₁ * (q (k - N₁).toNat).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1)))) := by
  letI := localBorel ℚ v
  have hN1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hX0 : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1)) ≠ 0 := natCast_cpow_neg_ne_zero _ hN1 _

  have hZ := LanglandsTunnell.CubicInduction.hasSum_shell_localZeta30_one_iotaGL_scalarPi_zpow_of_iotaGL_invariant
    v Φ hΦK hπ hϖ k σ₀ hconv s hs

  have hsummand : (fun j : ℤ =>
        (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}).toReal : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-((j : ℂ) * (s - 1))) *
          Φ (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ j * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k))) =
      fun j : ℤ => (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}).toReal : ℂ) *
        (Φ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ j))) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ j) := by
    funext j
    rw [iotaGL_diagZ_mul_scalarPi_zpow, natCast_cpow_neg_int_mul]
    ring
  rw [hsummand] at hZ

  obtain ⟨S, hS, hSD⟩ := exists_hasSum_row_and_mul_eval_eq
    (fun n : ℤ × ℤ => Φ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1))))
    N₁ hsupp D₁ q r hrow k hk _ hX hX0
  have hZ' : HasSum (fun j : ℤ => (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}).toReal : ℂ) *
        (Φ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ j))) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ j))
      ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}).toReal : ℂ) * S) := hS.mul_left _
  rw [hZ.unique hZ', mul_assoc, hSD]

theorem exists_forall_lt_re_localZeta30_iotaGL_scalarPi_zpow_mul_eval_eq
    (Φ : LocalGL3 v → ℂ)
    (hΦK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, Φ (g * iotaGL k) = Φ g)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (N₁ : ℤ) (D₁ : Polynomial ℂ) (q : ℕ → Polynomial ℂ) (r : ℝ) (hr : 0 < r)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) →
      Φ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1))) = 0)
    (hrow : ∀ (j : ℕ) (X : ℂ), ‖X‖ < r →
      Summable (fun m₁ : ℕ =>
        ‖Φ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (j : ℤ)) * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (m₁ : ℤ))))) * X ^ m₁‖) ∧
      (∑' m₁ : ℕ, Φ (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (j : ℤ)) * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₁ + (m₁ : ℤ))))) * X ^ m₁) *
          D₁.eval X = (q j).eval X)
    (k : ℤ) (hk : N₁ ≤ k) (σ₀ : ℝ)
    (hconv : letI := localBorel ℚ v
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) Φ 1 (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) σ₀) :
    letI := localBorel ℚ v
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) Φ 1 s (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) * D₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) =
        (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}).toReal : ℂ) *
          (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ N₁ * (q (k - N₁).toNat).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1)))) := by
  letI := localBorel ℚ v
  have hN1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨σ₁, hσ₁⟩ := exists_forall_lt_re_norm_cpow_neg_sub_one_lt (Ideal.absNorm v.asIdeal) hN1 hr
  refine ⟨max σ₀ σ₁, fun s hs => ?_⟩
  exact localZeta30_iotaGL_scalarPi_zpow_mul_eval_eq v Φ hΦK hπ hϖ N₁ D₁ q r hsupp hrow k hk σ₀ hconv s
    (lt_of_le_of_lt (le_max_left _ _) hs) (hσ₁ s (lt_of_le_of_lt (le_max_right _ _) hs))

section RatTaylor

open Finset

theorem summable_norm_coeff_mul_pow (Q : Polynomial ℂ) (x : ℂ) :
    Summable fun n : ℕ => ‖Q.coeff n * x ^ n‖ := by
  refine summable_of_ne_finset_zero (s := range (Q.natDegree + 1)) fun n hn => ?_
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn), zero_mul, norm_zero]

theorem tsum_coeff_mul_pow (Q : Polynomial ℂ) (x : ℂ) : ∑' n : ℕ, Q.coeff n * x ^ n = Q.eval x := by
  rw [tsum_eq_sum (s := range (Q.natDegree + 1)) fun n hn => ?_, Polynomial.eval_eq_sum_range]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn), zero_mul]

theorem eval_mul_tsum_eq_eval_of_convolution (P Q : Polynomial ℂ) (c : ℕ → ℂ)
    (hc : ∀ n : ℕ, ∑ ij ∈ antidiagonal n, c ij.1 * Q.coeff ij.2 = P.coeff n)
    (X₀ : ℂ) (hs : Summable fun n : ℕ => ‖c n * X₀ ^ n‖) :
    Q.eval X₀ * ∑' n : ℕ, c n * X₀ ^ n = P.eval X₀ := by
  rw [← tsum_coeff_mul_pow Q X₀, mul_comm,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs (summable_norm_coeff_mul_pow Q X₀),
    ← tsum_coeff_mul_pow P X₀]
  refine tsum_congr fun n => ?_
  rw [← hc n, sum_mul]
  refine sum_congr rfl fun ij hij => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [← hij, pow_add]
  ring

theorem eval_mul_eq_eval_of_convolution_of_hasSum (P Q : Polynomial ℂ) (c : ℕ → ℂ)
    (hc : ∀ n : ℕ, ∑ ij ∈ antidiagonal n, c ij.1 * Q.coeff ij.2 = P.coeff n)
    (X₀ S : ℂ) (hs : Summable fun n : ℕ => ‖c n * X₀ ^ n‖) (hS : HasSum (fun n : ℕ => c n * X₀ ^ n) S) :
    Q.eval X₀ * S = P.eval X₀ := by
  rw [← hS.tsum_eq]
  exact eval_mul_tsum_eq_eval_of_convolution P Q c hc X₀ hs

theorem powerSeries_mul_coe_cancel {f g : PowerSeries ℂ} {q : Polynomial ℂ} (hq : q ≠ 0)
    (h : f * (q : PowerSeries ℂ) = g * (q : PowerSeries ℂ)) : f = g :=
  mul_right_cancel₀ (fun h0 => hq (Polynomial.coe_eq_zero_iff.mp h0)) h

theorem coeff_mul_coe (f : PowerSeries ℂ) (q : Polynomial ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * (q : PowerSeries ℂ)) =
      ∑ ij ∈ antidiagonal n, PowerSeries.coeff ij.1 f * q.coeff ij.2 := by
  rw [PowerSeries.coeff_mul]
  simp only [Polynomial.coeff_coe]

theorem convolution_of_mk_mul_coe_eq_coe (c : ℕ → ℂ) (q p : Polynomial ℂ)
    (h : PowerSeries.mk c * (q : PowerSeries ℂ) = (p : PowerSeries ℂ)) :
    ∀ n : ℕ, ∑ ij ∈ antidiagonal n, c ij.1 * q.coeff ij.2 = p.coeff n := fun n => by
  have := congrArg (PowerSeries.coeff n) h
  rw [coeff_mul_coe, Polynomial.coeff_coe] at this
  simpa only [PowerSeries.coeff_mk] using this

theorem eval_mul_tsum_eq_eval_of_mk_mul_coe_eq_coe (c : ℕ → ℂ) (q p : Polynomial ℂ)
    (h : PowerSeries.mk c * (q : PowerSeries ℂ) = (p : PowerSeries ℂ))
    (X₀ : ℂ) (hs : Summable fun n : ℕ => ‖c n * X₀ ^ n‖) :
    q.eval X₀ * ∑' n : ℕ, c n * X₀ ^ n = p.eval X₀ :=
  eval_mul_tsum_eq_eval_of_convolution p q c (convolution_of_mk_mul_coe_eq_coe c q p h) X₀ hs

end RatTaylor
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

section Transpose

theorem vec2_comp_swap (X Y : ℂ) : (![X, Y] : Fin 2 → ℂ) ∘ (Equiv.swap (0 : Fin 2) 1) = ![Y, X] := by
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

theorem torusShape_transpose (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ)
    (r : ℝ)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (h : ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ => ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
        MvPolynomial.eval ![X, Y] P) :
    (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A (n.2, n.1) = 0) ∧
    (∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ => ‖A (N₁ + (m.2 : ℤ), N₁ + (m.1 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, A (N₁ + (m.2 : ℤ), N₁ + (m.1 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₂.eval X * D₁.eval Y) =
        MvPolynomial.eval ![X, Y] (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P)) := by
  refine ⟨fun n hn => hsupp (n.2, n.1) (hn.symm), fun X Y hX hY => ?_⟩
  obtain ⟨hs, hid⟩ := h Y X hY hX
  have hfunN : (fun m : ℕ × ℕ => ‖A (N₁ + (m.2 : ℤ), N₁ + (m.1 : ℤ)) * X ^ m.1 * Y ^ m.2‖) =
      (fun m : ℕ × ℕ => ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * Y ^ m.1 * X ^ m.2‖) ∘ (Equiv.prodComm ℕ ℕ) := by
    funext m; simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]; ring_nf
  refine ⟨?_, ?_⟩
  · rw [hfunN]; exact (Equiv.summable_iff _).2 hs
  · have ht : (∑' m : ℕ × ℕ, A (N₁ + (m.2 : ℤ), N₁ + (m.1 : ℤ)) * X ^ m.1 * Y ^ m.2) =
        ∑' m : ℕ × ℕ, A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * Y ^ m.1 * X ^ m.2 := by
      rw [← (Equiv.prodComm ℕ ℕ).tsum_eq (fun m : ℕ × ℕ => A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) * Y ^ m.1 * X ^ m.2)]
      exact tsum_congr fun m => by simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]; ring
    rw [ht, MvPolynomial.eval_rename, vec2_comp_swap, mul_comm (D₂.eval X), hid]

end Transpose
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

end Ws1.Middle.Eval
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

noncomputable section

namespace Ws1
namespace Middle
namespace Laurent

open Finset Polynomial

theorem summable_norm_shift (a : ℤ → ℂ) (z : ℂ) (ha : Summable fun n : ℤ => ‖a n * z ^ n‖) (j : ℤ) :
    Summable fun n : ℤ => ‖a (n - j) * z ^ (n - j)‖ :=
  (Equiv.subRight j).summable_iff.2 ha

theorem tsum_shift (a : ℤ → ℂ) (z : ℂ) (j : ℤ) :
    ∑' n : ℤ, a (n - j) * z ^ (n - j) = ∑' n : ℤ, a n * z ^ n :=
  (Equiv.subRight j).tsum_eq (fun n : ℤ => a n * z ^ n)

theorem tsum_mul_monomial (a : ℤ → ℂ) (z : ℂ) (hz : z ≠ 0) (c : ℂ) (j : ℕ) :
    (∑' n : ℤ, a n * z ^ n) * (c * z ^ j) = ∑' n : ℤ, c * a (n - (j : ℤ)) * z ^ n := by
  rw [← tsum_shift a z (j : ℤ), ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [zpow_sub₀ hz, zpow_natCast]
  field_simp

theorem summable_norm_monomial_term (a : ℤ → ℂ) (z : ℂ) (hz : z ≠ 0) (ha : Summable fun n : ℤ => ‖a n * z ^ n‖)
    (c : ℂ) (j : ℕ) : Summable fun n : ℤ => ‖c * a (n - (j : ℤ)) * z ^ n‖ := by
  have h := (summable_norm_shift a z ha (j : ℤ)).mul_left (‖c‖ * ‖z ^ j‖)
  refine h.congr fun n => ?_
  rw [zpow_sub₀ hz, zpow_natCast, norm_mul, norm_mul, norm_mul, norm_div]
  field_simp

theorem summable_norm_conv_mul_zpow (a : ℤ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (ha : Summable fun n : ℤ => ‖a n * z ^ n‖) (p : Polynomial ℂ) :
    Summable fun n : ℤ => ‖(∑ j ∈ p.support, p.coeff j * a (n - (j : ℤ))) * z ^ n‖ := by
  have h : Summable fun n : ℤ => ∑ j ∈ p.support, ‖p.coeff j * a (n - (j : ℤ)) * z ^ n‖ :=
    summable_sum fun j _ => summable_norm_monomial_term a z hz ha (p.coeff j) j
  refine h.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  rw [sum_mul]
  exact norm_sum_le _ _

theorem tsum_mul_eval_eq_tsum_conv (a : ℤ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (ha : Summable fun n : ℤ => ‖a n * z ^ n‖) (p : Polynomial ℂ) :
    (∑' n : ℤ, a n * z ^ n) * p.eval z = ∑' n : ℤ, (∑ j ∈ p.support, p.coeff j * a (n - (j : ℤ))) * z ^ n := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, mul_sum]
  simp_rw [tsum_mul_monomial a z hz, sum_mul]
  rw [Summable.tsum_finsetSum]
  intro j _
  exact (summable_norm_monomial_term a z hz ha (p.coeff j) j).of_norm

theorem rpow_int_le_add {r₁ r r₂ : ℝ} (h₁ : 0 < r₁) (h12 : r₁ ≤ r) (h23 : r ≤ r₂) (n : ℤ) :
    r ^ n ≤ r₁ ^ n + r₂ ^ n := by
  have hr : 0 < r := lt_of_lt_of_le h₁ h12
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, zpow_natCast, zpow_natCast]
    exact le_add_of_nonneg_of_le (pow_nonneg h₁.le _) (pow_le_pow_left₀ hr.le h23 _)
  · rw [zpow_neg, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast]
    exact le_add_of_le_of_nonneg (inv_anti₀ (pow_pos h₁ _) (pow_le_pow_left₀ h₁.le h12 _))
      (inv_nonneg.2 (pow_nonneg (hr.le.trans h23) _))

theorem summable_norm_mul_pow_of_le_of_le (a : ℤ → ℂ) {r₁ r r₂ : ℝ} (h₁ : 0 < r₁) (h12 : r₁ ≤ r)
    (h23 : r ≤ r₂) (hs₁ : Summable fun n : ℤ => ‖a n‖ * r₁ ^ n) (hs₂ : Summable fun n : ℤ => ‖a n‖ * r₂ ^ n) :
    Summable fun n : ℤ => ‖a n‖ * r ^ n := by
  have hr : 0 < r := lt_of_lt_of_le h₁ h12
  refine (hs₁.add hs₂).of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (zpow_pos hr n).le) fun n => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (rpow_int_le_add h₁ h12 h23 n) (norm_nonneg _)

theorem summable_norm_mul_zpow_iff (a : ℤ → ℂ) (z : ℂ) :
    (Summable fun n : ℤ => ‖a n * z ^ n‖) ↔ Summable fun n : ℤ => ‖a n‖ * ‖z‖ ^ n := by
  refine summable_congr fun n => ?_
  rw [norm_mul, norm_zpow]

theorem exists_sub_interval_avoiding (F : Finset ℝ) {r₁ r₂ : ℝ} (h12 : r₁ < r₂) :
    ∃ r₁' r₂' : ℝ, r₁ < r₁' ∧ r₁' < r₂' ∧ r₂' < r₂ ∧ ∀ x ∈ F, ¬ (r₁' ≤ x ∧ x ≤ r₂') := by
  classical

  let G : Finset ℝ := insert r₂ (F.filter fun x => r₁ < x)
  have hG : G.Nonempty := ⟨r₂, mem_insert_self _ _⟩
  have hmin : r₁ < G.min' hG := by
    refine (Finset.lt_min'_iff G hG).2 fun y hy => ?_
    rcases mem_insert.1 hy with rfl | hy
    · exact h12
    · exact (mem_filter.1 hy).2
  set m := G.min' hG with hm
  have hm2 : m ≤ r₂ := G.min'_le _ (mem_insert_self _ _)
  refine ⟨r₁ + (m - r₁) / 3, r₁ + 2 * (m - r₁) / 3, by linarith, by linarith, by linarith, ?_⟩
  rintro x hx ⟨hx1, hx2⟩
  have hxr : r₁ < x := by linarith
  have hxG : x ∈ G := mem_insert_of_mem (mem_filter.2 ⟨hx, hxr⟩)
  have := G.min'_le x hxG
  linarith

theorem eq_zero_of_tsum_mul_eval_eq_zero (e : ℤ → ℂ) {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hs₁ : Summable fun n : ℤ => ‖e n‖ * r₁ ^ n) (hs₂ : Summable fun n : ℤ => ‖e n‖ * r₂ ^ n)
    (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hz : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → (∑' n : ℤ, e n * z ^ n) * Q.eval z = 0) : e = 0 := by
  classical
  obtain ⟨r₁', r₂', h1, h2, h3, havoid⟩ :=
    exists_sub_interval_avoiding ((Q.roots.toFinset).image (‖·‖)) h12
  have h0' : 0 < r₁' := h0.trans h1
  refine Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero e h0' h2
    (summable_norm_mul_pow_of_le_of_le e h0 h1.le (h2.le.trans h3.le) hs₁ hs₂)
    (summable_norm_mul_pow_of_le_of_le e h0 (h1.le.trans h2.le) h3.le hs₁ hs₂) fun z hz1 hz2 => ?_
  have hQz : Q.eval z ≠ 0 := by
    intro hroot
    have hmem : ‖z‖ ∈ (Q.roots.toFinset).image (‖·‖) :=
      mem_image.2 ⟨z, Multiset.mem_toFinset.2 ((Polynomial.mem_roots hQ).2 hroot), rfl⟩
    exact havoid _ hmem ⟨hz1.le, hz2.le⟩
  have := hz z (h1.trans hz1) (hz2.trans h3)
  exact (mul_eq_zero.1 this).resolve_right hQz

end Ws1.Middle.Laurent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace Ws1
namespace Middle
namespace Cells

variable (v : HeightOneSpectrum (𝓞 ℚ))

def yShell (k : ℤ) : Set (v.adicCompletion ℚ) := {y | Valued.v y = WithZero.exp k}

def aShell (n : ℤ) : Set (v.adicCompletion ℚ)ˣ := {a | Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-n)}

variable {v}

def dualCellIntegrand {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (V : LocalGL3 v → ℂ) (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (s : ℂ)
    (y : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) : ℂ :=
  letI := localBorel ℚ v
  fD (w₀ * unipotentGL2 y) *
    (((χD 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1) *
      localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 a * unipotentGL2 y)))

def dualCell {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (V : LocalGL3 v → ℂ) (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (w₀ : GL (Fin 2) (v.adicCompletion ℚ))
    (k n : ℤ) (s : ℂ) : ℂ :=
  letI := localBorel ℚ v
  ∫ y in yShell v k, (∫ a in aShell v n, dualCellIntegrand hπ V ℓ χD fD w₀ s y a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)

section Comm
variable {K : Type*} [Field K]
theorem scalarPi_comm' (π : K) (hπ : π ≠ 0) (g : GL (Fin 2) K) :
    UnramifiedWhittaker.scalarPi π hπ * g = g * UnramifiedWhittaker.scalarPi π hπ := by
  refine Units.ext ?_
  have h : ((UnramifiedWhittaker.scalarPi π hπ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      π • (1 : Matrix (Fin 2) (Fin 2) K) := by
    show (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) K) = π • 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [Units.val_mul, Units.val_mul, h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
theorem scalarPi_zpow_comm' (π : K) (hπ : π ≠ 0) (g : GL (Fin 2) K) (n : ℤ) :
    g * UnramifiedWhittaker.scalarPi π hπ ^ n = UnramifiedWhittaker.scalarPi π hπ ^ n * g :=
  (((show Commute (UnramifiedWhittaker.scalarPi π hπ) g from scalarPi_comm' π hπ g).zpow_left n).eq).symm
theorem diagUnits2_one_mul (x y : Kˣ) : diagUnits2 (1 : Kˣ) (x * y) = diagUnits2 1 x * diagUnits2 1 y := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_diagUnits2, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
end Comm
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

theorem exists_unit_of_mem_aShell {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (n : ℤ) (a : (v.adicCompletion ℚ)ˣ) (ha : a ∈ aShell v n) :
    ∃ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 ∧ a = (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ n * e := by
  refine ⟨(Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ (-n) * a, ?_, by group⟩
  have hmk : Valued.v ((Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    rw [Units.val_mk0]; exact hϖ
  have ha' : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-n) := ha
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hmk, ha', ← WithZero.exp_zsmul,
    ← WithZero.exp_add]
  simp

theorem unramified_apply_of_mem_aShell {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χ e = 1)
    (n : ℤ) (a : (v.adicCompletion ℚ)ˣ) (ha : a ∈ aShell v n) :
    ((χ a : ℂˣ) : ℂ) = ((χ (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n := by
  obtain ⟨e, he, rfl⟩ := exists_unit_of_mem_aShell hπ hϖ n a ha
  rw [map_mul, hχ e he, mul_one, map_zpow, Units.val_zpow_eq_zpow_val]

theorem modulus_cpow_of_mem_aShell (n : ℤ) (a : (v.adicCompletion ℚ)ˣ) (ha : a ∈ aShell v n) (s : ℂ) :
    ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) := by
  letI := localBorel ℚ v
  have hmod := (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v).2.2.2.1 n a ha
  rw [hmod, show (1 - s) - 1 = -s by ring]
  have hq : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hx : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-n) := zpow_pos hq _
  have hqC : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.cpow_def_of_ne_zero hqC,
    ← Complex.ofReal_log hx.le, Real.log_zpow, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  have : Complex.log (Ideal.absNorm v.asIdeal : ℂ) = ((Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [show (Ideal.absNorm v.asIdeal : ℂ) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_log hq.le]
  rw [this]
  push_cast
  ring

theorem dualTwist_iotaGL_invariant {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (V : LocalGL3 v → ℂ)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g) (ℓ : ℕ)
    (k : GL (Fin 2) (v.adicCompletion ℚ)) (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) (g : LocalGL3 v) :
    (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (g * iotaGL k) = (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) g := by
  show dualWhittakerFn3 V (g * iotaGL k * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))) =
    dualWhittakerFn3 V (g * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))
  rw [mul_assoc, ← map_mul, scalarPi_zpow_comm', map_mul, ← mul_assoc]
  exact hVdK k hk _

theorem localZeta31_mul_iotaGL (W : LocalGL3 v → ℂ)
    (hWK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, W (g * iotaGL k) = W g)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v)
    (k : GL (Fin 2) (v.adicCompletion ℚ)) (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    letI := localBorel ℚ v
    localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ s (g * iotaGL k) = localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ s g := by
  letI := localBorel ℚ v
  simp only [localZeta31, ← mul_assoc, hWK k hk]

theorem diagUnits2_unipotentGL2_mem {e : (v.adicCompletion ℚ)ˣ} (he : Valued.v (e : v.adicCompletion ℚ) = 1)
    {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1) :
    diagUnits2 1 e * unipotentGL2 y ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  refine Subgroup.mul_mem _ ?_ (Ws1.Middle.DualD23.unipotentGL2_mem_K2 v hy)
  have he' : Valued.v (((e⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, he, inv_one]
  refine Ws1.Middle.DualD23.mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [coe_diagUnits2]; fin_cases i <;> fin_cases j <;> simp [he]
  · have : (((diagUnits2 (1 : (v.adicCompletion ℚ)ˣ) e)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
        !![1, 0; 0, ((e⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] := rfl
    rw [this]; fin_cases i <;> fin_cases j <;> simp [he]

theorem dualCellIntegrand_bulk_eq {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (V : LocalGL3 v → ℂ)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχDu : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
    (α₀ : ℂ) (hα₀ : ((χD 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₀)
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hfDK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → fD (g * k) = fD g)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) (k : ℤ) (hk : k ≤ 0) (n : ℤ)
    (y : v.adicCompletion ℚ) (hy : y ∈ yShell v k) (a : (v.adicCompletion ℚ)ˣ) (ha : a ∈ aShell v n) :
    letI := localBorel ℚ v
    dualCellIntegrand hπ V ℓ χD fD w₀ s y a =
      fD 1 * (α₀ ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) *
        localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)))) := by
  letI := localBorel ℚ v
  have hy1 : Valued.v y ≤ 1 := by
    rw [show Valued.v y = _ from hy, ← WithZero.exp_zero, WithZero.exp_le_exp]; exact hk
  obtain ⟨e, he, rfl⟩ := exists_unit_of_mem_aShell hπ hϖ n a ha
  have hfD1 : fD (w₀ * unipotentGL2 y) = fD 1 := by
    have := hfDK (w₀ * unipotentGL2 y) 1
      (Subgroup.mul_mem _ (Ws1.Middle.DualD23.w0_mem_K2 v hw₀) (Ws1.Middle.DualD23.unipotentGL2_mem_K2 v hy1))
    rwa [one_mul] at this
  have hχ := unramified_apply_of_mem_aShell hπ hϖ (χD 0) (hχDu 0) n _ ha
  have hmod := modulus_cpow_of_mem_aShell (v := v) n _ ha s
  have hpt : iotaGL (diagUnits2 1 ((Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ n * e) * unipotentGL2 y) =
      iotaGL (diagUnits2 1 ((Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ n)) * iotaGL (diagUnits2 1 e * unipotentGL2 y) := by
    rw [diagUnits2_one_mul, mul_assoc, map_mul]
  unfold dualCellIntegrand
  rw [hfD1, hχ, hα₀, hmod, hpt,
    localZeta31_mul_iotaGL _ (dualTwist_iotaGL_invariant hπ V hVdK ℓ) _ _ _ _ (diagUnits2_unipotentGL2_mem he hy1)]

theorem dualCell_bulk_eq {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (V : LocalGL3 v → ℂ)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχDu : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
    (α₀ : ℂ) (hα₀ : ((χD 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₀)
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hfDK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → fD (g * k) = fD g)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) (k : ℤ) (hk : k ≤ 0) (hmeasY : letI := localBorel ℚ v; MeasurableSet (yShell v k)) (n : ℤ) :
    letI := localBorel ℚ v
    dualCell hπ V ℓ χD fD w₀ k n s =
      ((((selfDualHaarAt ℚ v) (yShell v k)).toReal : ℝ) : ℂ) * (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
        (fD 1 * (α₀ ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) *
          localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)))))) := by
  letI := localBorel ℚ v
  have H := LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v
  have hmeasA : MeasurableSet (aShell v n) := H.1 n
  have hmassA : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (aShell v n) = (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1} := by
    rw [show aShell v n = {y : (v.adicCompletion ℚ)ˣ | Valued.v (y : v.adicCompletion ℚ) = WithZero.exp (-(n))} from rfl,
      (H.2.2.1 n).1, neg_zero, WithZero.exp_zero]
  unfold dualCell
  have hinner : ∀ y ∈ yShell v k,
      (∫ a in aShell v n, dualCellIntegrand hπ V ℓ χD fD w₀ s y a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) =
        ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (fD 1 * (α₀ ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) *
          localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))))) := by
    intro y hy
    rw [setIntegral_congr_fun hmeasA (fun a ha =>
      dualCellIntegrand_bulk_eq hπ hϖ V hVdK ℓ χD hχDu α₀ hα₀ fD hfDK w₀ hw₀ s k hk n y hy a ha),
      setIntegral_const, measureReal_def, hmassA, Complex.real_smul]
  rw [setIntegral_congr_fun hmeasY hinner, setIntegral_const, measureReal_def, Complex.real_smul]

theorem dualWhittakerFn3_dualTwist {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (V : LocalGL3 v → ℂ) (ℓ : ℕ) :
    dualWhittakerFn3 (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) =
      fun g => V (g * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))) := by

  let τ₂ : GL (Fin 2) (v.adicCompletion ℚ) →* GL (Fin 2) (v.adicCompletion ℚ) :=
    { toFun := transposeInvN (Fin 2)
      map_one' := Units.ext (by rw [coe_transposeInvN, inv_one, Units.val_one, Matrix.transpose_one])
      map_mul' := transposeInvN_mul (Fin 2) }
  have hsym : Matrix.transpose ((UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      ((UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    show Matrix.transpose (!![algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ, 0; 0,
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ] : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = _
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hsc : transposeInvN (Fin 2) (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)⁻¹ := by
    refine Units.ext ?_
    rw [coe_transposeInvN, Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hsym]
  have hτc : transposeInvN (Fin 2) (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))) = UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ) := by
    change τ₂ (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))) = _
    rw [map_zpow, show τ₂ (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)⁻¹ from hsc, inv_zpow, zpow_neg, inv_inv]
  have hw : transposeInv3 (longWeyl3 : LocalGL3 v) = longWeyl3 := by
    refine Units.ext ?_
    rw [Ws1.Middle.DualKit.transposeInv3_coe, Ws1.Middle.DualKit.longWeyl3_inv, longWeyl3_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  funext g
  show V (longWeyl3 * transposeInv3 (longWeyl3 * transposeInv3 g * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) = _
  rw [Ws1.Middle.DualKit.transposeInv3_mul, Ws1.Middle.DualKit.transposeInv3_mul,
    Ws1.Middle.DualKit.transposeInv3_transposeInv3, hw, Ws1.Middle.DualKit.transposeInv3_iotaGL, hτc,
    ← mul_assoc, ← mul_assoc, Ws1.Middle.DualKit.longWeyl3_mul_self, one_mul]

theorem exists_cpow_modulus_of_unramified {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χ e = 1)
    (α : ℂ) (hα : ((χ (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α) :
    ∃ t : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ t = α⁻¹ ∧
      ∀ a : (v.adicCompletion ℚ)ˣ, ((χ a : ℂˣ) : ℂ) = ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ t := by
  letI := localBorel ℚ v
  have hq : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hq1 : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hlog : Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := (Real.log_pos hq1).ne'
  have hqC : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hα0 : α ≠ 0 := by rw [← hα]; exact Units.ne_zero _
  have hlogq : Complex.log (Ideal.absNorm v.asIdeal : ℂ) = ((Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [show (Ideal.absNorm v.asIdeal : ℂ) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_log hq.le]
  set L : ℂ := ((Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) with hL
  have hL0 : L ≠ 0 := by rw [hL]; exact_mod_cast hlog
  refine ⟨Complex.log α⁻¹ / L, ?_, fun a => ?_⟩
  · rw [Complex.cpow_def_of_ne_zero hqC, hlogq, show L * (Complex.log α⁻¹ / L) = Complex.log α⁻¹ by field_simp,
      Complex.exp_log (inv_ne_zero hα0)]
  ·
    obtain ⟨n, hn, -⟩ := (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v).2.1 a
    have hχa := unramified_apply_of_mem_aShell hπ hϖ χ hχ n a hn
    have hmod := (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v).2.2.2.1 n a hn
    rw [hχa, hα, hmod]
    have hx : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-n) := zpow_pos hq _
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, Real.log_zpow,
      Complex.ofReal_mul, Complex.ofReal_intCast, ← hL,
      show (((-n : ℤ) : ℂ) * L) * (Complex.log α⁻¹ / L) = ((-n : ℤ) : ℂ) * Complex.log α⁻¹ by
        field_simp,
      show ((-n : ℤ) : ℂ) * Complex.log α⁻¹ = (-n : ℤ) * Complex.log α⁻¹ by norm_cast,
      Complex.exp_int_mul, Complex.exp_log (inv_ne_zero hα0), zpow_neg, inv_zpow, inv_inv]

theorem diagUnits2_mul_zpow_eq_scalarPi_zpow_mul_diagUnitGL2 {K : Type*} [Field K] (π : K) (hπ : π ≠ 0)
    (a : Kˣ) (n : ℤ) :
    diagUnits2 (a * Units.mk0 π hπ ^ n) (Units.mk0 π hπ ^ n) = UnramifiedWhittaker.scalarPi π hπ ^ n * diagUnitGL2 a := by

  let d : Kˣ × Kˣ →* GL (Fin 2) K :=
    { toFun := fun p => diagUnits2 p.1 p.2
      map_one' := by
        refine Units.ext ?_
        simp only [coe_diagUnits2, Prod.fst_one, Prod.snd_one, Units.val_one]
        ext i j; fin_cases i <;> fin_cases j <;> simp
      map_mul' := by
        intro p r
        refine Units.ext ?_
        simp only [coe_diagUnits2, Prod.fst_mul, Prod.snd_mul, Units.val_mul]
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] }
  have hd : ∀ x y : Kˣ, diagUnits2 x y = d (x, y) := fun _ _ => rfl
  have hsc : UnramifiedWhittaker.scalarPi π hπ = d (Units.mk0 π hπ, Units.mk0 π hπ) := by
    refine Units.ext ?_
    show ((UnramifiedWhittaker.scalarPi π hπ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((diagUnits2 (Units.mk0 π hπ) (Units.mk0 π hπ) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    rw [coe_diagUnits2]; rfl
  have h1 : diagUnitGL2 a = d (a, 1) := by rw [← diagUnits2_one_right]; rfl
  rw [hd, hsc, h1, ← map_zpow, ← map_mul, show ((a * Units.mk0 π hπ ^ n, Units.mk0 π hπ ^ n) : Kˣ × Kˣ) =
    (Units.mk0 π hπ, Units.mk0 π hπ) ^ n * (a, 1) by
      rw [Prod.pow_mk, Prod.mk_mul_mk, mul_one, mul_comm]]

theorem phi0_firstSlot_invariant {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (V : LocalGL3 v → ℂ)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (ℓ : ℕ) (ε : (v.adicCompletion ℚ)ˣ) (hε : Valued.v (ε : v.adicCompletion ℚ) = 1)
    (A : LocalGL3 v) (k : ℤ) :
    (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (A * iotaGL (diagUnitGL2 ε) * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) = (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (A * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) := by

  have hcomm : iotaGL (diagUnitGL2 ε) * (weylPrime3 : LocalGL3 v) = weylPrime3 * iotaGL (diagUnitGL2 ε) := by
    refine Units.ext ?_
    simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [embedMat2, weylPrime3, Matrix.mul_apply, Fin.sum_univ_three]

  have hc2 : ∀ m : ℤ, diagUnitGL2 ε * UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m = UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m * diagUnitGL2 ε := fun m => scalarPi_zpow_comm' _ _ _ m
  have hmem : diagUnitGL2 ε ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
    rw [← diagUnits2_one_right]
    have he' : Valued.v (((ε⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hε, inv_one]
    refine Ws1.Middle.DualD23.mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
    · rw [coe_diagUnits2]; fin_cases i <;> fin_cases j <;> simp [hε]
    · have : (((diagUnits2 ε (1 : (v.adicCompletion ℚ)ˣ))⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
          !![((ε⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 0; 0, 1] := rfl
      rw [this]; fin_cases i <;> fin_cases j <;> simp [hε]
  show V (A * iotaGL (diagUnitGL2 ε) * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k) * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ)))) =
    V (A * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k) * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))
  have : A * iotaGL (diagUnitGL2 ε) * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k) * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))) =
      A * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k) * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))) * iotaGL (diagUnitGL2 ε) := by
    rw [mul_assoc A, ← map_mul, hc2, map_mul, ← mul_assoc A, mul_assoc (A * _), ← mul_assoc (iotaGL (diagUnitGL2 ε)),
      hcomm, mul_assoc (weylPrime3 : LocalGL3 v), ← map_mul, hc2, map_mul]
    simp only [mul_assoc]
  rw [this, hVK _ hmem]

theorem modulus_cpow_of_mem_aShell' (n : ℤ) (a : (v.adicCompletion ℚ)ˣ) (ha : a ∈ aShell v n) (w : ℂ) :
    ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ w = ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ n := by
  letI := localBorel ℚ v
  have hmod := (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v).2.2.2.1 n a ha
  rw [hmod]
  have hq : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hx : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-n) := zpow_pos hq _
  have hqC : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.cpow_def_of_ne_zero hqC,
    ← Complex.ofReal_log hx.le, Real.log_zpow, Complex.ofReal_mul, Complex.ofReal_intCast, ← Complex.exp_int_mul]
  congr 1
  have : Complex.log (Ideal.absNorm v.asIdeal : ℂ) = ((Real.log ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [show (Ideal.absNorm v.asIdeal : ℂ) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_log hq.le]
  rw [this]; push_cast; ring

theorem diagUnitGL2_mul {K : Type*} [Field K] (x y : Kˣ) : diagUnitGL2 (x * y) = diagUnitGL2 x * diagUnitGL2 y := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_diagUnitGL2]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem localZeta30_phi0_hasSum_shells {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (V : LocalGL3 v → ℂ)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (ℓ : ℕ) (k : ℤ) (s : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
        (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (diagUnitGL2 a) * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) * (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) :
    letI := localBorel ℚ v
    HasSum (fun m : ℤ => ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
        ((fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m))) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ m))
      (localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) 1 s (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k))) := by
  letI := localBorel ℚ v
  have H := LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v
  have hmeas := H.1
  have hmass := fun n => (H.2.2.1 n).1
  have hsum := H.2.2.2.2 _ hint
  simp only [localZeta30]
  have hcell : ∀ m : ℤ,
      (∫ a in {y : (v.adicCompletion ℚ)ˣ | Valued.v (y : v.adicCompletion ℚ) = WithZero.exp (-(m))},
        (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (diagUnitGL2 a) * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) * (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) =
      ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * ((fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m))) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ m) := by
    intro m
    have hconst : ∀ a ∈ {y : (v.adicCompletion ℚ)ˣ | Valued.v (y : v.adicCompletion ℚ) = WithZero.exp (-(m))},
        (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (diagUnitGL2 a) * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) * (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
        (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m))) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ m := by
      intro a ha
      obtain ⟨e, he, hae⟩ := exists_unit_of_mem_aShell hπ hϖ m a ha
      rw [modulus_cpow_of_mem_aShell' (v := v) m a ha (s - 1), MonoidHom.one_apply, Units.val_one, mul_one, hae,
        diagUnitGL2_mul, map_mul, phi0_firstSlot_invariant hπ V hVK ℓ e he, ← map_mul, scalarPi_zpow_comm']
    rw [setIntegral_congr_fun (hmeas m) hconst, setIntegral_const, measureReal_def, hmass m, Complex.real_smul,
      neg_zero, WithZero.exp_zero]
  have hfun : (fun m : ℤ => ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
        ((fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m))) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ m)) =
      fun m : ℤ => ∫ a in {y : (v.adicCompletion ℚ)ˣ | Valued.v (y : v.adicCompletion ℚ) = WithZero.exp (-(m))},
        (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (diagUnitGL2 a) * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ k)) * (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    funext m; rw [hcell m]
  rw [hfun]
  exact hsum

theorem dual_point_value {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (W : LocalGL3 v → ℂ) (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W) (ℓ : ℕ) (n : ℤ) (a : (v.adicCompletion ℚ)ˣ) :
    dualWhittakerFn3 (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))))
        (iotaGL (diagUnitGL2 a) * (weylPrime3 * transposeInv3 (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))))) =
      (((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n)⁻¹ * (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (diagUnitGL2 a) * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) := by
  have hu0 : (unipotentGL2 (0 : v.adicCompletion ℚ) : GL (Fin 2) (v.adicCompletion ℚ)) = 1 := by
    refine Units.ext ?_; rw [unipotentGL2_coe, Units.val_one]; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hl0 : (lowerUnipotent21 (-(0 : v.adicCompletion ℚ)) : LocalGL3 v) = 1 := by
    refine Units.ext ?_; rw [lowerUnipotent21_coe, Units.val_one]; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hpt := Ws1.DualPoint.iotaGL_diagUnitGL2_mul_weylPrime3_transposeInv3 a (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n) (0 : v.adicCompletion ℚ)
  rw [hu0, mul_one, hl0, mul_one] at hpt
  rw [dualWhittakerFn3_dualTwist hπ V ℓ]
  show V (iotaGL (diagUnitGL2 a) * (weylPrime3 * transposeInv3 (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)))) *
      iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))) = _
  rw [hpt, diagUnits2_mul_zpow_eq_scalarPi_zpow_mul_diagUnitGL2, mul_assoc, mul_assoc,
    Ws1.Middle.DualD23.central_of_mem_gl3CyclicSubspace hω hVmem, map_inv, Units.val_inv_eq_inv_val, map_zpow,
    Units.val_zpow_eq_zpow_val, ← scalarPi_zpow_comm', map_mul]

theorem localZeta30_dual_point_eq {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (W : LocalGL3 v → ℂ) (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W) (ℓ : ℕ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (n : ℤ) :
    letI := localBorel ℚ v
    localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (dualWhittakerFn3 (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))))) χ s
        (weylPrime3 * transposeInv3 (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)))) =
      (((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n)⁻¹ *
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) χ s (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) := by
  letI := localBorel ℚ v
  simp only [localZeta30]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  beta_reduce
  rw [dual_point_value hπ W ωv hω V hVmem ℓ n a]
  ring

theorem isLocalZeta30ConvergentAbove_dual_point {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (W : LocalGL3 v → ℂ) (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W) (ℓ : ℕ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (σ : ℝ) (n : ℤ)
    (h : letI := localBorel ℚ v
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (dualWhittakerFn3 (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))))) χ
        (weylPrime3 * transposeInv3 (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)))) σ) :
    letI := localBorel ℚ v
    IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) χ (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) σ := by
  letI := localBorel ℚ v
  intro s hs
  have hint := (h s hs).const_mul (((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n)
  refine hint.congr (Filter.Eventually.of_forall fun a => ?_)
  show ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n * (dualWhittakerFn3 (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))))
      (iotaGL (diagUnitGL2 a) * (weylPrime3 * transposeInv3 (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))))) *
      ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) = _
  rw [dual_point_value hπ W ωv hω V hVmem ℓ n a]
  have hω0 : ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  field_simp

theorem LRep1_eq_of_forall_lt_re {q : ℕ} (hq : 1 < q) {f g : ℂ → ℂ}
    (hf : Ws1.Middle.Laurent1.LRep1 q f) (hg : Ws1.Middle.Laurent1.LRep1 q g) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → f s = g s) : ∀ s : ℂ, f s = g s := by
  obtain ⟨Pf, Mf, hPf⟩ := hf
  obtain ⟨Pg, Mg, hPg⟩ := hg
  have hpoly : Pf * Polynomial.X ^ Mg = Pg * Polynomial.X ^ Mf := by
    refine Ws1.Middle.Eval.polynomial_eq_of_forall_lt_re_eval_eq q hq σ _ _ fun s hs => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hPf s, ← hPg s, h s hs]
    ring
  intro s
  have hx : ((q : ℂ) ^ (-s)) ≠ 0 := Ws1.Middle.Laurent1.x_ne_zero hq s
  have h1 := hPf s
  have h2 := hPg s
  have h3 := congrArg (Polynomial.eval ((q : ℂ) ^ (-s))) hpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at h3
  have : f s * ((q : ℂ) ^ (-s)) ^ Mf * ((q : ℂ) ^ (-s)) ^ Mg = g s * ((q : ℂ) ^ (-s)) ^ Mg * ((q : ℂ) ^ (-s)) ^ Mf := by
    rw [h1, h2, h3]
  have hMM : ((q : ℂ) ^ (-s)) ^ Mf * ((q : ℂ) ^ (-s)) ^ Mg ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hx)
  calc f s = f s * (((q : ℂ) ^ (-s)) ^ Mf * ((q : ℂ) ^ (-s)) ^ Mg) / (((q : ℂ) ^ (-s)) ^ Mf * ((q : ℂ) ^ (-s)) ^ Mg) := by
        field_simp
    _ = g s * (((q : ℂ) ^ (-s)) ^ Mg * ((q : ℂ) ^ (-s)) ^ Mf) / (((q : ℂ) ^ (-s)) ^ Mf * ((q : ℂ) ^ (-s)) ^ Mg) := by
        rw [← mul_assoc, ← mul_assoc, this]
    _ = g s := by field_simp

set_option maxHeartbeats 3200000 in

theorem localZeta31_dualTwist_lattice_eq_zero
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (hE : E ≠ 0) (hEd : Ed ≠ 0) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g = (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ * ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) (u : ℂ)
    (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχDu : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
    (hα₁ : ((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)))
    (N₀ : ℤ) (D₀₁ D₀₂ : Polynomial ℂ) (P₀ : MvPolynomial (Fin 2) ℂ) (r₀ : ℝ)
    (hTD₀ : IsTorusDatum v hπ (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) N₀ D₀₁ D₀₂ P₀ r₀)
    (row₀ : ℕ → Polynomial ℂ)
    (hrow₀ : ∀ (j : ℕ) (X : ℂ), ‖X‖ < r₀ →
      Summable (fun m₁ : ℕ =>
        ‖(fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₀ + (j : ℤ)) * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₀ + (m₁ : ℤ))))) * X ^ m₁‖) ∧
      (∑' m₁ : ℕ, (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₀ + (j : ℤ)) * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₀ + (m₁ : ℤ))))) * X ^ m₁) *
          D₀₁.eval X = (row₀ j).eval X)
    (n : ℤ) (hn : n < N₀) :
    letI := localBorel ℚ v
    ∃ σn : ℝ, IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) σn ∧
      ∀ s : ℂ, σn < (1 - s).re →
      localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) = 0 := by
  letI := localBorel ℚ v
  have hq1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqC : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hqz : ∀ z : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ z ≠ 0 := fun z => by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hqC
  have ha1 : (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) ≠ 0 := mul_ne_zero (left_ne_zero_of_mul ha) (hqz _)
  have hA1 : dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) ≠ 0 := by
    unfold dualAlpha1; exact mul_ne_zero (hqz _) (inv_ne_zero ha1)
  have hχu' : ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → (χD 1)⁻¹ e = 1 := fun e he => by
    rw [MonoidHom.inv_apply, hχDu 1 e he, inv_one]
  have hαinv : (((χD 1)⁻¹ (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)))⁻¹ := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hα₁]
  obtain ⟨t, hqt, hχt⟩ := exists_cpow_modulus_of_unramified hπ hϖ (χD 1)⁻¹ hχu' _ hαinv
  rw [inv_inv] at hqt
  have hmem' : dualWhittakerFn3 (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) ∈ gl3CyclicSubspace W := by
    rw [dualWhittakerFn3_dualTwist hπ V ℓ]; exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hVmem
  obtain ⟨Q₁, Q₂, kk, σ₀, σ₁, hQ₂, hc0, hZ0, hc1, hZ1⟩ :=
    TransportKit.transport_dual v W E Ed hE ε ℓ h31 (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) hmem' t (χD 1)⁻¹ hχt (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)))
  have hii : ((χD 1)⁻¹)⁻¹ = χD 1 := by ext a; simp [MonoidHom.inv_apply]
  rw [hii] at hZ1 hc1
  have hconvΦ := isLocalZeta30ConvergentAbove_dual_point hπ W ωv hω V hVmem ℓ (χD 1)⁻¹ σ₀ n hc0
  have hχt1 : ∀ a : (v.adicCompletion ℚ)ˣ, (((χD 1)⁻¹ a : ℂˣ) : ℂ) =
      (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ t := by
    intro a; rw [hχt a, MonoidHom.one_apply, Units.val_one, one_mul]
  have hone : ∀ a : (v.adicCompletion ℚ)ˣ, (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) =
      (((χD 1)⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-t) := by
    intro a
    rw [hχt a, ← Complex.cpow_add _ _ (TransportKit.modulus_units_ne_zero v a), add_neg_cancel, Complex.cpow_zero,
      MonoidHom.one_apply, Units.val_one]
  have hconv1 := TransportKit.isLocalZeta30ConvergentAbove_twist v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (χD 1)⁻¹ 1 (-t) hone _ σ₀ hconvΦ
  obtain ⟨hD₀₁0, hD₀₂0, hr₀, hsupp₀, hser₀⟩ := hTD₀

  have hZ0zero : ∀ s'' : ℂ, σ₀ - (-t).re < s''.re →
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) 1 s'' (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) = 0 := by
    intro s'' hs''
    have hZ := localZeta30_phi0_hasSum_shells hπ hϖ V hVK ℓ n s'' (hconv1 s'' hs'')
    have hzero : (fun m : ℤ => ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
        ((fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m))) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s'' - 1))) ^ m)) = fun _ => 0 := by
      funext m
      rw [hsupp₀ (m, n) (Or.inr hn)]; ring
    rw [hzero] at hZ
    exact hZ.unique hasSum_zero

  have hQ1 : Q₁ = 0 := by
    refine Ws1.Middle.Eval.polynomial_eq_of_forall_lt_re_eval_eq (Ideal.absNorm v.asIdeal) hq1 (max σ₀ (σ₀ - (-t).re - t.re)) Q₁ 0
      (fun s' hs' => ?_)
    have hs0 : σ₀ < s'.re := lt_of_le_of_lt (le_max_left _ _) hs'
    have hs3 : σ₀ - (-t).re < (s' + t).re := by
      have := lt_of_le_of_lt (le_max_right _ _) hs'; rw [Complex.add_re]; linarith
    have h0 := hZ0 s' hs0
    rw [localZeta30_dual_point_eq hπ W ωv hω V hVmem ℓ (χD 1)⁻¹ s' n,
      TransportKit.localZeta30_twist v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) 1 (χD 1)⁻¹ t hχt1 s', hZ0zero (s' + t) hs3] at h0
    simp only [mul_zero, zero_mul] at h0
    rw [Polynomial.eval_zero]
    simpa [Nat.cast_id] using (mul_eq_zero.mp h0.symm).resolve_right (hqz _)

  obtain ⟨σQ, hσQ⟩ := Ws1.Middle.Laurent1.exists_forall_eval_cmul_qs_ne_zero hq1 Q₂ hQ₂ (((Ideal.absNorm v.asIdeal : ℂ))⁻¹) (inv_ne_zero hqC)
  refine ⟨max σ₁ σQ, fun w hw => hc1 w (lt_of_le_of_lt (le_max_left _ _) hw), fun s hs => ?_⟩
  have hs1 : σ₁ < (1 - s).re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsQ : σQ < (1 - s).re := lt_of_le_of_lt (le_max_right _ _) hs
  have hQ2s : Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ≠ 0 := by
    have := hσQ (1 - s) hsQ
    rwa [show ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) by
      rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hqC, Complex.cpow_one, ← mul_assoc,
        inv_mul_cancel₀ hqC, one_mul]] at this
  have hZ1s := hZ1 s hs1
  rw [hQ1, Polynomial.eval_zero, zero_mul, zero_mul] at hZ1s
  exact (mul_eq_zero.mp hZ1s).resolve_right hQ2s

set_option maxHeartbeats 3200000 in

theorem localZeta31_dualTwist_lattice_eq
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (hE : E ≠ 0) (hEd : Ed ≠ 0) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g = (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ * ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) (u : ℂ)
    (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχDu : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
    (hα₁ : ((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)))
    (N₀ : ℤ) (D₀₁ D₀₂ : Polynomial ℂ) (P₀ : MvPolynomial (Fin 2) ℂ) (r₀ : ℝ)
    (hTD₀ : IsTorusDatum v hπ (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) N₀ D₀₁ D₀₂ P₀ r₀)
    (row₀ : ℕ → Polynomial ℂ)
    (hrow₀ : ∀ (j : ℕ) (X : ℂ), ‖X‖ < r₀ →
      Summable (fun m₁ : ℕ =>
        ‖(fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₀ + (j : ℤ)) * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₀ + (m₁ : ℤ))))) * X ^ m₁‖) ∧
      (∑' m₁ : ℕ, (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₀ + (j : ℤ)) * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (N₀ + (m₁ : ℤ))))) * X ^ m₁) *
          D₀₁.eval X = (row₀ j).eval X)
    (n : ℤ) (hn : N₀ ≤ n) :
    letI := localBorel ℚ v
    ∃ σn : ℝ, IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) σn ∧
      ∀ s : ℂ, σn < (1 - s).re →
      localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) *
        Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
        D₀₁.eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) =
      ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ *
        E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
        (((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n)⁻¹ *
        (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
          ((dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) ^ N₀ * (row₀ (n - N₀).toNat).eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s))) := by
  letI := localBorel ℚ v
  have hq1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqC : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hqz : ∀ z : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ z ≠ 0 := fun z => by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hqC
  have ha1 : (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) ≠ 0 := mul_ne_zero (left_ne_zero_of_mul ha) (hqz _)
  have hA1 : dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) ≠ 0 := by
    unfold dualAlpha1; exact mul_ne_zero (hqz _) (inv_ne_zero ha1)

  have hχu' : ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → (χD 1)⁻¹ e = 1 := fun e he => by
    rw [MonoidHom.inv_apply, hχDu 1 e he, inv_one]
  have hαinv : (((χD 1)⁻¹ (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)))⁻¹ := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hα₁]
  obtain ⟨t, hqt, hχt⟩ := exists_cpow_modulus_of_unramified hπ hϖ (χD 1)⁻¹ hχu' _ hαinv
  rw [inv_inv] at hqt

  have hmem' : dualWhittakerFn3 (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) ∈ gl3CyclicSubspace W := by
    rw [dualWhittakerFn3_dualTwist hπ V ℓ]; exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hVmem
  obtain ⟨Q₁, Q₂, kk, σ₀, σ₁, hQ₂, hc0, hZ0, hc1, hZ1⟩ :=
    TransportKit.transport_dual v W E Ed hE ε ℓ h31 (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) hmem' t (χD 1)⁻¹ hχt (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)))
  have hii : ((χD 1)⁻¹)⁻¹ = χD 1 := by ext a; simp [MonoidHom.inv_apply]
  rw [hii] at hZ1 hc1

  have hconvΦ := isLocalZeta30ConvergentAbove_dual_point hπ W ωv hω V hVmem ℓ (χD 1)⁻¹ σ₀ n hc0
  have hχt1 : ∀ a : (v.adicCompletion ℚ)ˣ, (((χD 1)⁻¹ a : ℂˣ) : ℂ) =
      (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ t := by
    intro a; rw [hχt a, MonoidHom.one_apply, Units.val_one, one_mul]
  have hone : ∀ a : (v.adicCompletion ℚ)ˣ, (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) =
      (((χD 1)⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-t) := by
    intro a
    rw [hχt a, ← Complex.cpow_add _ _ (TransportKit.modulus_units_ne_zero v a), add_neg_cancel, Complex.cpow_zero,
      MonoidHom.one_apply, Units.val_one]
  have hconv1 := TransportKit.isLocalZeta30ConvergentAbove_twist v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (χD 1)⁻¹ 1 (-t) hone _ σ₀ hconvΦ

  obtain ⟨hD₀₁0, hD₀₂0, hr₀, hsupp₀, hser₀⟩ := hTD₀
  obtain ⟨σX, hσX⟩ := Ws1.Middle.Eval.exists_forall_lt_re_norm_cpow_neg_sub_one_lt (Ideal.absNorm v.asIdeal) hq1 hr₀
  have hrow_closed : ∀ s'' : ℂ, max (σ₀ - (-t).re) σX < s''.re →
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) 1 s'' (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) * D₀₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s'' - 1))) =
        ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s'' - 1))) ^ N₀ * (row₀ (n - N₀).toNat).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s'' - 1)))) := by
    intro s'' hs''
    have hs1 : σ₀ - (-t).re < s''.re := lt_of_le_of_lt (le_max_left _ _) hs''
    have hs2 : σX < s''.re := lt_of_le_of_lt (le_max_right _ _) hs''
    have hZ := localZeta30_phi0_hasSum_shells hπ hϖ V hVK ℓ n s'' (hconv1 s'' hs1)
    obtain ⟨S, hS, hSD⟩ := Ws1.Middle.Eval.exists_hasSum_row_and_mul_eval_eq
      (fun p : ℤ × ℤ => (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2 * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.1))))
      N₀ hsupp₀ D₀₁ row₀ r₀ hrow₀ n hn _ (hσX s'' hs2) (hqz _)
    rw [(hZ.unique (hS.mul_left _)), mul_assoc, hSD]

  have hF : ∀ s' : ℂ, max (max σ₀ (max (σ₀ - (-t).re) σX - t.re)) 0 < s'.re →
      (((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n)⁻¹ * (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-((s' + t) - 1))) ^ N₀ *
          (row₀ (n - N₀).toNat).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-((s' + t) - 1))))) * Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s')) =
        Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s')) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kk : ℂ) * s') * D₀₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-((s' + t) - 1))) := by
    intro s' hs'
    have hs0 : σ₀ < s'.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs'
    have hs3 : max (σ₀ - (-t).re) σX < (s' + t).re := by
      have := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs'
      rw [Complex.add_re]; linarith
    have h0 := hZ0 s' hs0
    rw [localZeta30_dual_point_eq hπ W ωv hω V hVmem ℓ (χD 1)⁻¹ s' n,
      TransportKit.localZeta30_twist v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) 1 (χD 1)⁻¹ t hχt1 s'] at h0
    have h4 := hrow_closed (s' + t) hs3
    rw [show -((s' + t) - 1) = -(s' + t - 1) by ring] at h4 ⊢

    have : (((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n)⁻¹ * (localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) 1 (s' + t) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) *
        D₀₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s' + t - 1)))) * Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s')) =
        Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s')) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kk : ℂ) * s') * D₀₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s' + t - 1))) := by
      rw [← h0]; ring
    rw [h4] at this
    exact this

  set c : ℂ := (Ideal.absNorm v.asIdeal : ℂ) * (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)))⁻¹ with hc
  have hc0 : c ≠ 0 := mul_ne_zero hqC (inv_ne_zero hA1)
  have hX1 : ∀ s' : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-((s' + t) - 1)) = c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s') := by
    intro s'
    rw [hc, show -((s' + t) - 1) = (1 : ℂ) + (-t) + (-s') by ring, Complex.cpow_add _ _ hqC, Complex.cpow_add _ _ hqC,
      Complex.cpow_one, Complex.cpow_neg, hqt]
  have hkk : ∀ s' : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ ((kk : ℂ) * s') = ((1 : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s'))⁻¹) ^ kk := by
    intro s'
    rw [one_mul, Complex.cpow_neg, inv_inv, ← Complex.cpow_int_mul]
  have hLHS : Ws1.Middle.Laurent1.LRep1 (Ideal.absNorm v.asIdeal) (fun s' : ℂ =>
      (((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n)⁻¹ * (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * ((c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s')) ^ N₀ *
          (row₀ (n - N₀).toNat).eval (c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s')))) * Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s'))) := by
    refine Ws1.Middle.Laurent1.mul hq1 (Ws1.Middle.Laurent1.smul hq1 _ (Ws1.Middle.Laurent1.smul hq1 _
      (Ws1.Middle.Laurent1.mul hq1 (Ws1.Middle.Laurent1.cx_zpow hq1 c hc0 N₀)
        (Ws1.Middle.Laurent1.polyEval hq1 _ (Ws1.Middle.Laurent1.smul hq1 c (Ws1.Middle.Laurent1.x hq1))))))
      (Ws1.Middle.Laurent1.polyEval hq1 _ (Ws1.Middle.Laurent1.x hq1))
  have hRHS : Ws1.Middle.Laurent1.LRep1 (Ideal.absNorm v.asIdeal) (fun s' : ℂ =>
      Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s')) * ((1 : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s'))⁻¹) ^ kk * D₀₁.eval (c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s'))) :=
    Ws1.Middle.Laurent1.mul hq1 (Ws1.Middle.Laurent1.mul hq1
      (Ws1.Middle.Laurent1.polyEval hq1 _ (Ws1.Middle.Laurent1.x hq1))
      (Ws1.Middle.Laurent1.cxinv_zpow hq1 1 one_ne_zero kk))
      (Ws1.Middle.Laurent1.polyEval hq1 _ (Ws1.Middle.Laurent1.smul hq1 c (Ws1.Middle.Laurent1.x hq1)))
  have hall := LRep1_eq_of_forall_lt_re hq1 hLHS hRHS _ (fun s' hs' => by
    have := hF s' hs'
    simp only [hX1, hkk] at this
    simpa only [Nat.cast_id] using this)

  obtain ⟨σQ, hσQ⟩ := Ws1.Middle.Laurent1.exists_forall_eval_cmul_qs_ne_zero hq1 Q₂ hQ₂ (((Ideal.absNorm v.asIdeal : ℂ))⁻¹) (inv_ne_zero hqC)
  obtain ⟨σE, hσE⟩ := Ws1.Middle.Laurent1.exists_forall_eval_cmul_q_one_sub_ne_zero hq1 Ed hEd
    ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) (mul_ne_zero (inv_ne_zero ha1) (hqz _))
  refine ⟨max σ₁ (max σQ σE), fun w hw => hc1 w (lt_of_le_of_lt (le_max_left _ _) hw), fun s hs => ?_⟩
  have hs1 : σ₁ < (1 - s).re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsQ : σQ < (1 - s).re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsE : σE < (1 - s).re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs

  have hQ2s : Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ≠ 0 := by
    have := hσQ (1 - s) hsQ
    rwa [show ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) by
      rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hqC, Complex.cpow_one, ← mul_assoc,
        inv_mul_cancel₀ hqC, one_mul]] at this

  have hEd1s : Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) ≠ 0 := by
    have := hσE (1 - s) hsE
    rwa [show (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - (1 - s)) =
        (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)) by
      rw [mul_assoc, ← Complex.cpow_add _ _ hqC]; congr 2; ring] at this

  have hA1def : dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ := rfl
  have hqt_inv : (Ideal.absNorm v.asIdeal : ℂ) ^ (-t) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) := by
    rw [Complex.cpow_neg, hqt, hA1def, mul_inv, inv_inv]; simp only [Complex.cpow_neg]
  have hdx : dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s = c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
    unfold dualX
    rw [hc, show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hqC, Complex.cpow_one]; ring
  have h_st : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + t)) = (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2)) := by
    rw [show -(s + t) = -s + -t by ring, Complex.cpow_add _ _ hqC, hqt_inv,
      show -(s + 1 / 2) = -s + -(1 / 2 : ℂ) by ring, Complex.cpow_add _ _ hqC]; ring
  have h_1st : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (s + t))) = (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)) := by
    rw [show -(1 - (s + t)) = t + -(1 - s) by ring, Complex.cpow_add _ _ hqC, hqt, hA1def,
      show -(1 / 2 - s) = (1 : ℂ) / 2 + -(1 - s) by ring, Complex.cpow_add _ _ hqC]; ring
  have h_ell : (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - (s + t))) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ := by
    rw [show (ℓ : ℂ) * (1 / 2 - (s + t)) = (ℓ : ℂ) * (1 / 2 - s) + (ℓ : ℕ) * (-t) by push_cast; ring,
      Complex.cpow_add _ _ hqC]
    congr 1
    rw [Complex.cpow_nat_mul, Complex.cpow_neg, hqt, inv_pow]
  have hγ : ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - (s + t))) * E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + t))) *
      (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (s + t)))))⁻¹ * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) =
      ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ * E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) := by
    have hEdinv : (Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))))⁻¹ * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) = 1 := inv_mul_cancel₀ hEd1s
    rw [h_st, h_1st, h_ell]
    calc _ = ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ * E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
          ((Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))))⁻¹ * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) := by ring
      _ = _ := by rw [hEdinv, mul_one]

  have hZ1s := hZ1 s hs1
  have halls := hall s
  rw [hdx]
  apply mul_right_cancel₀ hQ2s
  calc localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s)
          (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * D₀₁.eval (c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      = (localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s)
          (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) * Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * D₀₁.eval (c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by ring
    _ = Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * ((1 : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) ^ kk * D₀₁.eval (c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
          (ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - (s + t))) * E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + t))) *
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - (s + t)))))⁻¹ * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) := by rw [hZ1s, hkk]; ring
    _ = (((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ n)⁻¹ * (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * ((c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ N₀ *
          (row₀ (n - N₀).toNat).eval (c * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))) * Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
          (ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ * E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2)))) := by rw [← halls, hγ]
    _ = _ := by ring

end Ws1.Middle.Cells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

open MeasureTheory IsDedekindDomain NumberField Filter Topology
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction~exists_valued_eq_exp AutomorphicForm~lowerUnipotentGL2 UnramifiedWhittaker"

noncomputable section

namespace Ws46
namespace MidT1

theorem summable_norm_and_hasSum_setIntegral_of_partition {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (F : α → ℂ) (hF : Integrable F μ) (s : ι → Set α) (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Function.onFun Disjoint s)) (hcov : (⋃ i, s i) = Set.univ) :
    Summable (fun i => ‖∫ x in s i, F x ∂μ‖) ∧ HasSum (fun i => ∫ x in s i, F x ∂μ) (∫ x, F x ∂μ) := by
  have h1 : HasSum (fun i => ∫ x in s i, F x ∂μ) (∫ x in ⋃ i, s i, F x ∂μ) :=
    hasSum_integral_iUnion hm hd hF.integrableOn
  rw [hcov, Measure.restrict_univ] at h1
  refine ⟨?_, h1⟩
  have h2 : HasSum (fun i => ∫ x in s i, ‖F x‖ ∂μ) (∫ x in ⋃ i, s i, ‖F x‖ ∂μ) :=
    hasSum_integral_iUnion hm hd hF.norm.integrableOn
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) h2.summable
  exact norm_integral_le_integral_norm _

section Cells

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

open Ws1.Middle.Cells

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "K" => v.adicCompletion ℚ

scoped instance secondCountableTopology_units_adic : SecondCountableTopology (Kˣ) :=
  Units.isEmbedding_val₀.secondCountableTopology

def cellZ (kn : ℤ × ℤ) : Set (K × Kˣ) := yShell v kn.1 ×ˢ aShell v kn.2

def cellO : Option (ℤ × ℤ) → Set (K × Kˣ)
  | none => {0} ×ˢ Set.univ
  | some kn => cellZ v kn

theorem cellO_some (kn : ℤ × ℤ) : cellO v (some kn) = cellZ v kn := rfl
theorem cellO_none : cellO v none = {0} ×ˢ Set.univ := rfl

theorem pairwise_disjoint_yShell : Pairwise (Function.onFun Disjoint (yShell v)) := by
  intro k k' hne
  rw [Function.onFun, Set.disjoint_iff]
  rintro y ⟨hy, hy'⟩
  have : WithZero.exp k = WithZero.exp k' := by
    rw [← show Valued.v y = WithZero.exp k from hy]; exact hy'
  exact hne (WithZero.exp_injective this)

theorem pairwise_disjoint_aShell : Pairwise (Function.onFun Disjoint (aShell v)) := by
  intro m m' hne
  rw [Function.onFun, Set.disjoint_iff]
  rintro a ⟨ha, ha'⟩
  have : WithZero.exp (-m) = WithZero.exp (-m') := by
    rw [← show Valued.v (a : K) = WithZero.exp (-m) from ha]; exact ha'
  exact hne (neg_injective (WithZero.exp_injective this))

theorem iUnion_aShell : (⋃ m, aShell v m) = Set.univ := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hne : Valued.v (a : K) ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 a.ne_zero
  refine ⟨-WithZero.log (Valued.v (a : K)), ?_⟩
  show Valued.v (a : K) = WithZero.exp (-(-WithZero.log (Valued.v (a : K))))
  rw [neg_neg, WithZero.exp_log hne]

theorem mem_iUnion_yShell {y : K} (hy : y ≠ 0) : y ∈ ⋃ k, yShell v k := by
  simp only [Set.mem_iUnion]
  have hne : Valued.v y ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 hy
  exact ⟨WithZero.log (Valued.v y), show Valued.v y = _ by rw [WithZero.exp_log hne]⟩

theorem zero_not_mem_yShell (k : ℤ) : (0 : K) ∉ yShell v k := by
  intro h
  have h' : Valued.v (0 : K) = WithZero.exp k := h
  rw [map_zero] at h'
  exact WithZero.coe_ne_zero h'.symm

theorem pairwise_disjoint_cellO : Pairwise (Function.onFun Disjoint (cellO v)) := by
  rintro (_ | ⟨k, m⟩) (_ | ⟨k', m'⟩) hne
  · exact (hne rfl).elim
  · rw [Function.onFun, cellO_none, cellO_some, cellZ, Set.disjoint_prod]
    left
    rw [Set.disjoint_iff]
    rintro y ⟨hy0, hy⟩
    rw [Set.mem_singleton_iff] at hy0
    exact zero_not_mem_yShell v k' (hy0 ▸ hy)
  · rw [Function.onFun, cellO_none, cellO_some, cellZ, Set.disjoint_prod]
    left
    rw [Set.disjoint_iff]
    rintro y ⟨hy, hy0⟩
    rw [Set.mem_singleton_iff] at hy0
    exact zero_not_mem_yShell v k (hy0 ▸ hy)
  · rw [Function.onFun, cellO_some, cellO_some, cellZ, cellZ, Set.disjoint_prod]
    by_cases hk : k = k'
    · subst hk
      right
      exact pairwise_disjoint_aShell v (fun h => hne (by rw [show m = m' from h]))
    · left
      exact pairwise_disjoint_yShell v hk

theorem iUnion_cellO : (⋃ i, cellO v i) = Set.univ := by
  ext ⟨y, a⟩
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hy : y = 0
  · exact ⟨none, Set.mk_mem_prod (by simp [hy]) (Set.mem_univ _)⟩
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (mem_iUnion_yShell v hy)
    obtain ⟨m, hm⟩ : ∃ m, a ∈ aShell v m := by
      have := Set.mem_univ a; rw [← iUnion_aShell v] at this; exact Set.mem_iUnion.1 this
    exact ⟨some (k, m), Set.mk_mem_prod hk hm⟩

theorem exists_valued_eq_exp (k : ℤ) : ∃ y : K, y ≠ 0 ∧ Valued.v y = WithZero.exp k := by
  set ϖu : Kˣ := NumberField.AdelicLevel.uniformizerUnit ℚ v with hϖu
  have hϖ : Valued.v (ϖu : K) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ v
  refine ⟨((ϖu ^ (-k) : Kˣ) : K), Units.ne_zero _, ?_⟩
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]

theorem norm_eq_norm_iff (x y : K) : ‖x‖ = ‖y‖ ↔ Valued.v x = Valued.v y := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, NNReal.coe_inj,
    (WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).injective.eq_iff]

theorem measurableSet_yShell (k : ℤ) : MeasurableSet (yShell v k) := by
  obtain ⟨y₀, -, hy₀⟩ := exists_valued_eq_exp v k
  have h : yShell v k = (fun y : K => ‖y‖) ⁻¹' {‖y₀‖} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [norm_eq_norm_iff, hy₀]
    rfl
  rw [h]
  exact (isClosed_singleton.preimage continuous_norm).measurableSet

theorem measurableSet_aShell (n : ℤ) : MeasurableSet (aShell v n) := by
  obtain ⟨y₀, -, hy₀⟩ := exists_valued_eq_exp v (-n)
  have hm : Measurable (fun a : Kˣ => (a : K)) := by measurability
  have h : aShell v n = (fun a : Kˣ => ‖(a : K)‖) ⁻¹' {‖y₀‖} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [norm_eq_norm_iff, hy₀]
    rfl
  rw [h]
  exact (isClosed_singleton.preimage (continuous_norm.comp Units.continuous_val)).measurableSet

theorem measurableSet_cellO (i : Option (ℤ × ℤ)) : MeasurableSet (cellO v i) := by
  rcases i with _ | ⟨k, n⟩
  · exact (measurableSet_singleton 0).prod MeasurableSet.univ
  · exact (measurableSet_yShell v k).prod (measurableSet_aShell v n)

theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : K)).NeBot := by
  set ϖu : Kˣ := NumberField.AdelicLevel.uniformizerUnit ℚ v with hϖu
  have hϖ : Valued.v (ϖu : K) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ v
  have hnorm : ‖(ϖu : K)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hmem : (0 : K) ∈ closure {x : K | x ≠ 0} :=
    mem_closure_of_tendsto (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm)
      (Filter.Eventually.of_forall fun n => pow_ne_zero n (Units.ne_zero _))
  exact mem_closure_iff_nhdsWithin_neBot.mp hmem

theorem selfDualHaarAt_singleton (y : K) : selfDualHaarAt ℚ v {y} = 0 := by
  haveI := nhdsNE_zero_neBot v
  haveI : NullSingletonClass (selfDualHaarAt ℚ v) := Measure.IsAddHaarMeasure.nullSingletonClass _
  exact measure_singleton y

theorem measure_nullCell :
    ((selfDualHaarAt ℚ v).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure Kˣ))
      (cellO v none) = 0 := by
  rw [cellO_none, Measure.prod_prod, selfDualHaarAt_singleton, zero_mul]

theorem summable_and_hasSum_cellZ (F : K × Kˣ → ℂ)
    (hF : Integrable F ((selfDualHaarAt ℚ v).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))) :
    Summable (fun kn : ℤ × ℤ => ‖∫ x in cellZ v kn, F x
        ∂((selfDualHaarAt ℚ v).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))‖) ∧
    HasSum (fun kn : ℤ × ℤ => ∫ x in cellZ v kn, F x
        ∂((selfDualHaarAt ℚ v).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))))
      (∫ x, F x ∂((selfDualHaarAt ℚ v).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))) := by
  obtain ⟨hS, hH⟩ := summable_norm_and_hasSum_setIntegral_of_partition _ F hF (cellO v) (measurableSet_cellO v)
    (pairwise_disjoint_cellO v) (iUnion_cellO v)
  have h0 : ∫ x in cellO v none, F x
      ∂((selfDualHaarAt ℚ v).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) = 0 :=
    setIntegral_measure_zero _ (measure_nullCell v)
  have hrange : ∀ i ∉ Set.range (some : ℤ × ℤ → Option (ℤ × ℤ)),
      (fun i => ∫ x in cellO v i, F x
        ∂((selfDualHaarAt ℚ v).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))) i = 0 := by
    rintro (_ | kn) hi
    · exact h0
    · exact absurd (Set.mem_range_self kn) hi
  have hH' := ((Option.some_injective _).hasSum_iff hrange).mpr hH
  have hS' := hS.comp_injective (Option.some_injective _)
  exact ⟨hS', hH'⟩

theorem dual_unfold_eq_tsum_cells {v : HeightOneSpectrum (𝓞 ℚ)} {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (V : LocalGL3 v → ℂ) (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (s : ℂ)
    (hint : letI := localBorel ℚ v
      Integrable (fun ya : v.adicCompletion ℚ × (v.adicCompletion ℚ)ˣ => dualCellIntegrand hπ V ℓ χD fD w₀ s ya.1 ya.2)
        (((selfDualHaarAt ℚ v)).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))) :
    letI := localBorel ℚ v
    Summable (fun p : ℤ × ℤ => ‖dualCell hπ V ℓ χD fD w₀ p.1 p.2 s‖) ∧
    (∫ y, (∫ a, dualCellIntegrand hπ V ℓ χD fD w₀ s y a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) =
      ∑' p : ℤ × ℤ, dualCell hπ V ℓ χD fD w₀ p.1 p.2 s := by
  obtain ⟨hS, hH⟩ := summable_and_hasSum_cellZ v _ hint

  have hcell : ∀ p : ℤ × ℤ,
      ∫ x in cellZ v p, (fun ya : v.adicCompletion ℚ × (v.adicCompletion ℚ)ˣ => dualCellIntegrand hπ V ℓ χD fD w₀ s ya.1 ya.2) x
        ∂((selfDualHaarAt ℚ v).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) =
      dualCell hπ V ℓ χD fD w₀ p.1 p.2 s := by
    intro p
    rw [dualCell, cellZ, setIntegral_prod _ (hint.integrableOn)]
  simp_rw [hcell] at hS hH
  refine ⟨hS, ?_⟩
  rw [← integral_prod _ hint]
  exact hH.tsum_eq.symm

end Cells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

section Hint

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

open Ws1.Middle.Cells

theorem integrable_dualCellIntegrand {v : HeightOneSpectrum (𝓞 ℚ)} {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (V : LocalGL3 v → ℂ) (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (hfD : fD ∈ principalSeries2 v χD)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (hI : Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
        ((fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi
            (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (iotaGL g) * fD (w₀ * g)) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
            ((1 - s) - 1 / 2)) μ₂) :
    Integrable (fun ya : v.adicCompletion ℚ × (v.adicCompletion ℚ)ˣ => dualCellIntegrand hπ V ℓ χD fD w₀ s ya.1 ya.2)
      ((selfDualHaarAt ℚ v).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) := by
  set W' : LocalGL3 v → ℂ := fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))) with hW'
  set ν : Measure (v.adicCompletion ℚ) := selfDualHaarAt ℚ v with hν
  set τ : Measure (v.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) with hτ

  have h4 := LanglandsTunnell.RankinSelberg.integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
    v W' χD fD hfD w₀ hw₀ (1 - s) μ₂ τ ν hI

  set G : v.adicCompletion ℚ × (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → ℂ :=
    fun q => fD (w₀ * unipotentGL2 q.1) *
      (((χD 0 q.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1)) *
      (W' (iotaGL (diagUnitGL2 q.2.2.1) * lowerUnipotent21 q.2.2.2 * iotaGL (diagUnits2 1 q.2.1 * unipotentGL2 q.1)) *
        ((χD 1 q.2.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.2.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1)) with hG
  have h4' : Integrable G (ν.prod (τ.prod (τ.prod ν))) := h4
  have hmp := measurePreserving_prodAssoc ν τ (τ.prod ν)
  have h5 : Integrable (G ∘ (MeasurableEquiv.prodAssoc : (v.adicCompletion ℚ × (v.adicCompletion ℚ)ˣ) ×
      ((v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ) ≃ᵐ _)) ((ν.prod τ).prod (τ.prod ν)) :=
    (hmp.integrable_comp h4'.aestronglyMeasurable).mpr h4'
  have h6 := h5.integral_prod_left
  have h7 := h5.prod_right_ae

  refine h6.congr ?_
  filter_upwards [h7] with yt hyt
  obtain ⟨y, t⟩ := yt
  have hint2 : Integrable (fun ax : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ => G (y, t, ax)) (τ.prod ν) := hyt
  show (∫ ax : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ, G (y, t, ax) ∂(τ.prod ν)) = dualCellIntegrand hπ V ℓ χD fD w₀ s y t
  rw [integral_prod _ hint2]
  simp only [hG, hW', dualCellIntegrand, localZeta31]
  simp_rw [integral_const_mul]
  rw [mul_assoc]
  congr 1
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  dsimp only
  rw [integral_mul_const, integral_mul_const]

theorem dual_unfold_eq_tsum_cells_of_integrable {v : HeightOneSpectrum (𝓞 ℚ)} {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (V : LocalGL3 v → ℂ) (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (hfD : fD ∈ principalSeries2 v χD)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (hI : Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
        ((fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi
            (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (iotaGL g) * fD (w₀ * g)) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
            ((1 - s) - 1 / 2)) μ₂) :
    Summable (fun p : ℤ × ℤ => ‖dualCell hπ V ℓ χD fD w₀ p.1 p.2 s‖) ∧
    (∫ y, (∫ a, dualCellIntegrand hπ V ℓ χD fD w₀ s y a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) =
      ∑' p : ℤ × ℤ, dualCell hπ V ℓ χD fD w₀ p.1 p.2 s :=
  dual_unfold_eq_tsum_cells hπ hϖ V ℓ χD fD w₀ s (integrable_dualCellIntegrand hπ V ℓ χD fD hfD w₀ hw₀ s μ₂ hI)

end Hint
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23"

end Ws46.MidT1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1"

p2m_open "MeasureTheory IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker Filter Topology"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace Ws46
namespace MidT2

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

open Ws1.Middle.Cells

section Mat

variable {K : Type*} [Field K]

def lowerUnipotent2 (u : K) : GL (Fin 2) K where
  val := !![1, 0; u, 1]
  inv := !![1, 0; -u, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_lowerUnipotent2 (u : K) : ((lowerUnipotent2 u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; u, 1] := rfl
theorem coe_inv_lowerUnipotent2 (u : K) :
    (((lowerUnipotent2 u)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; -u, 1] := rfl

theorem lowerUnipotent2_mul_diagUnitGL2 (x : K) (t : Kˣ) :
    (lowerUnipotent2 x : GL (Fin 2) K) * diagUnitGL2 t = diagUnitGL2 t * lowerUnipotent2 ((t : K) * x) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_lowerUnipotent2, coe_lowerUnipotent2, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem lowerUnipotent21_eq_iotaGL (x : K) :
    (lowerUnipotent21 x : GL (Fin 3) K) = iotaGL (lowerUnipotent2 x) := by
  apply Units.ext
  simp only [coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, lowerUnipotent21, lowerUnipotent2]

theorem diagUnitGL2_mul_diagUnitGL2 (a b : Kˣ) : (diagUnitGL2 a : GL (Fin 2) K) * diagUnitGL2 b = diagUnitGL2 (a * b) := by
  rw [← diagHom_apply, ← diagHom_apply, ← diagHom_apply, map_mul]

theorem bruhat_tail (x : K) (a : Kˣ) (y : K) (hy : y ≠ 0) (w₀ : GL (Fin 2) K)
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0]) :
    (lowerUnipotent2 x : GL (Fin 2) K) * (diagUnits2 1 a * unipotentGL2 y) =
      lowerUnipotent2 ((a : K) * y⁻¹ + x) * (diagUnits2 (Units.mk0 y hy) (-(a * (Units.mk0 y hy)⁻¹)) * w₀) *
        lowerUnipotent2 y⁻¹ := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_lowerUnipotent2, coe_diagUnits2, unipotentGL2_coe, hw₀, Units.val_one, Units.val_neg,
    Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy] <;> field_simp <;> ring

theorem weyl_mul_unipotentGL2_eq (v : HeightOneSpectrum (𝓞 ℚ)) (y : v.adicCompletion ℚ) (hy : y ≠ 0)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    w₀ * unipotentGL2 y = upperUnipotent2 v y⁻¹ * diagonal2 v ![-(Units.mk0 y hy)⁻¹, Units.mk0 y hy] * lowerUnipotent2 y⁻¹ := by
  refine Units.ext ?_
  have hd : ((diagonal2 v ![-(Units.mk0 y hy)⁻¹, Units.mk0 y hy] : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![-y⁻¹, 0; 0, y] := by
    rw [diagonal2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Units.val_inv_eq_inv_val]
  simp only [Units.val_mul, hw₀, unipotentGL2_coe, upperUnipotent2_coe, hd, coe_lowerUnipotent2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy]

end Mat
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1"

theorem integral_comp_mul_left (v : HeightOneSpectrum (𝓞 ℚ)) (G : v.adicCompletion ℚ → ℂ)
    (t : v.adicCompletion ℚ) (ht : t ≠ 0) :
    ∫ x, G (t * x) ∂(selfDualHaarAt ℚ v) = ((modulus t : ℝ) : ℂ)⁻¹ * ∫ x, G x ∂(selfDualHaarAt ℚ v) := by
  have h := LanglandsTunnell.TateLocal.tateFourier_comp_mul_left (v.adicCompletion ℚ)
    (1 : AddChar (v.adicCompletion ℚ) ℂ) (selfDualHaarAt ℚ v) G t ht 0
  simpa [LanglandsTunnell.TateLocal.tateFourier] using h

theorem cpow_aux (X : ℂ) (hX : X ≠ 0) (σ : ℂ) : X⁻¹ * (X ^ (σ - 1))⁻¹ = X ^ (-σ) := by
  have h1 : X ^ σ = X ^ (σ - 1) * X := by
    conv_lhs => rw [show σ = (σ - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hX, Complex.cpow_one]
  rw [Complex.cpow_neg, h1, mul_inv, mul_comm]

theorem localZeta31_iotaGL_diagUnitGL2_mul {v : HeightOneSpectrum (𝓞 ℚ)} (F : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (σ : ℂ) (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v) :
    localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) F χ σ (iotaGL (diagUnitGL2 t) * h) =
      ((χ t : ℂˣ) : ℂ)⁻¹ * ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-σ) *
        localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) F χ σ h := by
  have ht0 : (t : v.adicCompletion ℚ) ≠ 0 := t.ne_zero
  have hmt : ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (modulus_pos ht0).ne'

  have inner : ∀ a' : (v.adicCompletion ℚ)ˣ,
      (∫ x, F (iotaGL (diagUnitGL2 a') * lowerUnipotent21 x * (iotaGL (diagUnitGL2 t) * h)) ∂(selfDualHaarAt ℚ v)) =
        ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ *
          ∫ x, F (iotaGL (diagUnitGL2 (t * a')) * lowerUnipotent21 x * h) ∂(selfDualHaarAt ℚ v) := by
    intro a'
    have hpt : ∀ x : v.adicCompletion ℚ, iotaGL (diagUnitGL2 a') * lowerUnipotent21 x * (iotaGL (diagUnitGL2 t) * h) =
        iotaGL (diagUnitGL2 (t * a')) * lowerUnipotent21 ((t : v.adicCompletion ℚ) * x) * h := by
      intro x
      rw [lowerUnipotent21_eq_iotaGL, lowerUnipotent21_eq_iotaGL, ← mul_assoc, mul_assoc (iotaGL _), ← map_mul,
        lowerUnipotent2_mul_diagUnitGL2, map_mul, ← mul_assoc, ← map_mul, diagUnitGL2_mul_diagUnitGL2, mul_comm a' t]
    simp_rw [hpt]
    exact integral_comp_mul_left v (fun x => F (iotaGL (diagUnitGL2 (t * a')) * lowerUnipotent21 x * h)) _ ht0

  unfold localZeta31
  simp_rw [inner]
  have key : ∀ a' : (v.adicCompletion ℚ)ˣ,
      ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ *
          (∫ x, F (iotaGL (diagUnitGL2 (t * a')) * lowerUnipotent21 x * h) ∂(selfDualHaarAt ℚ v)) *
        ((χ a' : ℂˣ) : ℂ) * ((modulus (a' : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (σ - 1) =
      (((χ t : ℂˣ) : ℂ)⁻¹ * ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-σ)) *
        (fun b : (v.adicCompletion ℚ)ˣ => (∫ x, F (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h) ∂(selfDualHaarAt ℚ v)) *
          ((χ b : ℂˣ) : ℂ) * ((modulus (b : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (σ - 1)) (t * a') := by
    intro a'
    have hχ : ((χ (t * a') : ℂˣ) : ℂ) = ((χ t : ℂˣ) : ℂ) * ((χ a' : ℂˣ) : ℂ) := by rw [map_mul, Units.val_mul]
    have hm : ((modulus ((t * a' : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (σ - 1) =
        ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (σ - 1) * ((modulus (a' : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (σ - 1) := by
      rw [Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    simp only []
    rw [hχ, hm, ← cpow_aux _ hmt σ]
    have hχt : ((χ t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hmt' : ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (σ - 1) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hmt
    field_simp
  simp_rw [key]
  have hsub := integral_mul_left_eq_self (μ := (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
    (fun b : (v.adicCompletion ℚ)ˣ => (∫ x, F (iotaGL (diagUnitGL2 b) * lowerUnipotent21 x * h) ∂(selfDualHaarAt ℚ v)) *
      ((χ b : ℂˣ) : ℂ) * ((modulus (b : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (σ - 1)) t
  rw [integral_const_mul, hsub]

section Tail

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem diagUnits2_eq_diagUnitGL2_mul {K : Type*} [Field K] (p q : Kˣ) :
    (diagUnits2 p q : GL (Fin 2) K) = diagUnitGL2 p * diagUnits2 1 q := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerUnipotent2_mem_K2 (v : HeightOneSpectrum (𝓞 ℚ)) {u : v.adicCompletion ℚ} (hu : Valued.v u ≤ 1) :
    (lowerUnipotent2 u : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  refine Ws1.Middle.DualD23.mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [coe_lowerUnipotent2]; fin_cases i <;> fin_cases j <;> simp [hu]
  · rw [coe_inv_lowerUnipotent2]; fin_cases i <;> fin_cases j <;> simp [hu, Valuation.map_neg]

theorem localZeta31_tail_point (F : LocalGL3 v → ℂ)
    (hFK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, F (g * iotaGL k) = F g)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (σ : ℂ) (a : (v.adicCompletion ℚ)ˣ) (y : v.adicCompletion ℚ) (hy : y ≠ 0)
    (hy1 : Valued.v y⁻¹ ≤ 1)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) F χ σ (iotaGL (diagUnits2 1 a * unipotentGL2 y)) =
      localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) F χ σ (iotaGL (diagUnits2 (Units.mk0 y hy) (-(a * (Units.mk0 y hy)⁻¹)))) := by
  unfold localZeta31
  refine integral_congr_ae (Filter.Eventually.of_forall fun a' => ?_)
  dsimp only
  congr 2
  have hpt : ∀ x : v.adicCompletion ℚ,
      F (iotaGL (diagUnitGL2 a') * lowerUnipotent21 x * iotaGL (diagUnits2 1 a * unipotentGL2 y)) =
        (fun x' : v.adicCompletion ℚ => F (iotaGL (diagUnitGL2 a') * lowerUnipotent21 x' *
          iotaGL (diagUnits2 (Units.mk0 y hy) (-(a * (Units.mk0 y hy)⁻¹))))) ((a : v.adicCompletion ℚ) * y⁻¹ + x) := by
    intro x
    dsimp only
    rw [lowerUnipotent21_eq_iotaGL, lowerUnipotent21_eq_iotaGL, mul_assoc, ← map_mul, bruhat_tail x a y hy w₀ hw₀,
      map_mul, map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, hFK _ (lowerUnipotent2_mem_K2 v hy1),
      hFK _ (Ws1.Middle.DualD23.w0_mem_K2 v hw₀)]
  simp_rw [hpt]
  exact integral_add_left_eq_self (μ := (selfDualHaarAt ℚ v))
    (fun x' : v.adicCompletion ℚ => F (iotaGL (diagUnitGL2 a') * lowerUnipotent21 x' *
      iotaGL (diagUnits2 (Units.mk0 y hy) (-(a * (Units.mk0 y hy)⁻¹))))) ((a : v.adicCompletion ℚ) * y⁻¹)

theorem section_tail (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (hfD : fD ∈ principalSeries2 v χD)
    (hfDK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → fD (g * k) = fD g)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (y : v.adicCompletion ℚ) (hy : y ≠ 0) (hy1 : Valued.v y⁻¹ ≤ 1) :
    fD (w₀ * unipotentGL2 y) =
      torusChar2 v χD ![-(Units.mk0 y hy)⁻¹, Units.mk0 y hy] * halfModulus2 v ![-(Units.mk0 y hy)⁻¹, Units.mk0 y hy] * fD 1 := by
  obtain ⟨-, hN, hT⟩ := mem_principalSeries2_iff.mp hfD
  rw [weyl_mul_unipotentGL2_eq v y hy w₀ hw₀, mul_assoc, hN, hT]
  have := hfDK (lowerUnipotent2 y⁻¹) 1 (lowerUnipotent2_mem_K2 v hy1)
  rw [one_mul] at this
  rw [this]

theorem torusChar2_pair (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (u₀ u₁ : (v.adicCompletion ℚ)ˣ) :
    torusChar2 v χD ![u₀, u₁] = ((χD 0 u₀ : ℂˣ) : ℂ) * ((χD 1 u₁ : ℂˣ) : ℂ) := by
  simp [torusChar2, Fin.prod_univ_two]

theorem halfModulus2_pair_inv (y : v.adicCompletion ℚ) (hy : y ≠ 0) :
    halfModulus2 v ![-(Units.mk0 y hy)⁻¹, Units.mk0 y hy] = (((‖y‖⁻¹ : ℝ)) : ℂ) := by
  unfold halfModulus2
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_neg, Units.val_inv_eq_inv_val,
    Units.val_mk0, norm_neg, norm_inv]
  rw [div_eq_mul_inv, ← sq, Real.sqrt_sq (inv_nonneg.mpr (norm_nonneg _))]

end Tail
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1"

theorem tail_alg (N α₀ α₁ Z f : ℂ) (n k : ℤ) (s : ℂ) (hN : N ≠ 0) (hα₀ : α₀ ≠ 0) (hα₁ : α₁ ≠ 0) :
    (α₀ ^ k * α₁ ^ (-k) * (N ^ ((k : ℤ) : ℂ))⁻¹ * f) *
        (α₀ ^ n * N ^ ((n : ℂ) * s) * ((α₁ ^ (-k))⁻¹ * N ^ (-(1 - s) * ((k : ℤ) : ℂ)) * Z)) =
      f * (N ^ (-(2 * (k : ℂ))) * (α₀ ^ (n + k) * N ^ (((n + k : ℤ) : ℂ) * s) * Z)) := by
  have hα₁k : α₁ ^ (-k) ≠ 0 := zpow_ne_zero _ hα₁
  have e1 : (N ^ ((k : ℤ) : ℂ))⁻¹ * N ^ ((n : ℂ) * s) * N ^ (-(1 - s) * ((k : ℤ) : ℂ)) =
      N ^ (-(2 * (k : ℂ))) * N ^ (((n + k : ℤ) : ℂ) * s) := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hN, ← Complex.cpow_add _ _ hN, ← Complex.cpow_add _ _ hN]
    congr 1
    push_cast
    ring
  calc (α₀ ^ k * α₁ ^ (-k) * (N ^ ((k : ℤ) : ℂ))⁻¹ * f) *
        (α₀ ^ n * N ^ ((n : ℂ) * s) * ((α₁ ^ (-k))⁻¹ * N ^ (-(1 - s) * ((k : ℤ) : ℂ)) * Z))
      = f * ((α₁ ^ (-k) * (α₁ ^ (-k))⁻¹) * ((α₀ ^ n * α₀ ^ k) *
          (((N ^ ((k : ℤ) : ℂ))⁻¹ * N ^ ((n : ℂ) * s) * N ^ (-(1 - s) * ((k : ℤ) : ℂ))) * Z))) := by ring
    _ = f * (N ^ (-(2 * (k : ℂ))) * (α₀ ^ (n + k) * N ^ (((n + k : ℤ) : ℂ) * s) * Z)) := by
      rw [mul_inv_cancel₀ hα₁k, one_mul, ← zpow_add₀ hα₀, e1]; ring

section Pointwise

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem dualCellIntegrand_tail_eq {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (V : LocalGL3 v → ℂ)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχDu : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
    (α₀ : ℂ) (hα₀ : ((χD 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₀)
    (α₁ : ℂ) (hα₁ : ((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₁)
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (hfD : fD ∈ principalSeries2 v χD)
    (hfDK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → fD (g * k) = fD g)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) (k : ℤ) (hk : 1 ≤ k) (n : ℤ)
    (y : v.adicCompletion ℚ) (hy : y ∈ yShell v k) (a : (v.adicCompletion ℚ)ˣ) (ha : a ∈ aShell v n) :
    dualCellIntegrand hπ V ℓ χD fD w₀ s y a =
      fD 1 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * (k : ℂ))) *
        (α₀ ^ (n + k) * (Ideal.absNorm v.asIdeal : ℂ) ^ (((n + k : ℤ) : ℂ) * s) *
          localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 ((Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ (n + k)))))) := by
  have hyv : Valued.v y = WithZero.exp k := hy
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hyv; exact WithZero.coe_ne_zero hyv.symm
  set yu : (v.adicCompletion ℚ)ˣ := Units.mk0 y hy0 with hyu
  have hyuv : Valued.v ((yu : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp k := by
    rw [hyu, Units.val_mk0]; exact hyv
  have hy1 : Valued.v y⁻¹ ≤ 1 := by
    rw [map_inv₀, hyv, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

  have hyu_shell : yu ∈ aShell v (-k) := by
    show Valued.v ((yu : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-(-k)); rw [neg_neg]; exact hyuv
  have hneg_shell : (-(yu⁻¹) : (v.adicCompletion ℚ)ˣ) ∈ aShell v k := by
    show Valued.v (((-(yu⁻¹) : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = WithZero.exp (-k)
    rw [Units.val_neg, Valuation.map_neg, Units.val_inv_eq_inv_val, map_inv₀, hyuv, WithZero.exp_neg]
  have hav : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-n) := ha
  have hay_shell : (-(a * yu⁻¹) : (v.adicCompletion ℚ)ˣ) ∈ aShell v (n + k) := by
    show Valued.v (((-(a * yu⁻¹) : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = WithZero.exp (-(n + k))
    rw [Units.val_neg, Valuation.map_neg, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hav, hyuv,
      ← WithZero.exp_neg, ← WithZero.exp_add]
    congr 1; ring

  have H := LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v
  have hq : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hα₀0 : α₀ ≠ 0 := by rw [← hα₀]; exact Units.ne_zero _
  have hα₁0 : α₁ ≠ 0 := by rw [← hα₁]; exact Units.ne_zero _

  have hmody : (modulus y : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(-k)) := H.2.2.2.1 (-k) yu hyu_shell
  have hmodyC : ((modulus y : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℤ) : ℂ) := by
    rw [hmody, neg_neg]; push_cast; exact (Complex.cpow_intCast _ _).symm
  have hnormy : ((‖y‖⁻¹ : ℝ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℤ) : ℂ))⁻¹ := by
    rw [← hmodyC, Complex.ofReal_inv]
    congr 1
    rw [show ‖y‖ = ((‖y‖₊ : NNReal) : ℝ) from rfl, ← LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v y]
  have hmodcpow : ((modulus ((yu : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 - s)) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (((-k : ℤ)) * (1 - s) : ℂ) := by
    rw [show (-(1 - s) : ℂ) = (1 - (1 - s)) - 1 by ring]
    exact modulus_cpow_of_mem_aShell (v := v) (-k) yu hyu_shell (1 - s)

  have hsec : fD (w₀ * unipotentGL2 y) = α₀ ^ k * α₁ ^ (-k) * ((Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℤ) : ℂ))⁻¹ * fD 1 := by
    rw [section_tail χD fD hfD hfDK w₀ hw₀ y hy0 hy1, torusChar2_pair, halfModulus2_pair_inv y hy0, hnormy,
      unramified_apply_of_mem_aShell hπ hϖ (χD 0) (hχDu 0) k _ hneg_shell, hα₀,
      unramified_apply_of_mem_aShell hπ hϖ (χD 1) (hχDu 1) (-k) _ hyu_shell, hα₁]
  have hχa : ((χD 0 a : ℂˣ) : ℂ) = α₀ ^ n := by
    rw [unramified_apply_of_mem_aShell hπ hϖ (χD 0) (hχDu 0) n a ha, hα₀]
  have hmoda := modulus_cpow_of_mem_aShell (v := v) n a ha s

  obtain ⟨e, he, hae⟩ := exists_unit_of_mem_aShell hπ hϖ (n + k) _ hay_shell
  have heK : diagUnits2 1 e ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
    simpa using diagUnits2_unipotentGL2_mem he (show Valued.v (0 : v.adicCompletion ℚ) ≤ 1 by simp)
  have hZ : localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 a * unipotentGL2 y)) =
      (α₁ ^ (-k))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s) * ((k : ℤ) : ℂ)) *
        localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 ((Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ (n + k)))) := by
    rw [localZeta31_tail_point _ (dualTwist_iotaGL_invariant hπ V hVdK ℓ) _ _ a y hy0 hy1 w₀ hw₀,
      diagUnits2_eq_diagUnitGL2_mul, map_mul, localZeta31_iotaGL_diagUnitGL2_mul,
      unramified_apply_of_mem_aShell hπ hϖ (χD 1) (hχDu 1) (-k) _ hyu_shell, hα₁, hmodcpow, hae, diagUnits2_one_mul,
      map_mul, localZeta31_mul_iotaGL _ (dualTwist_iotaGL_invariant hπ V hVdK ℓ) _ _ _ _ heK]
    congr 2
    push_cast
    ring
  unfold dualCellIntegrand
  rw [hsec, hχa, hmoda, hZ]
  exact tail_alg _ α₀ α₁ _ (fD 1) n k s hN0 hα₀0 hα₁0

end Pointwise
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1"

section Cell

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem dualCell_tail_eq {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (V : LocalGL3 v → ℂ)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχDu : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
    (α₀ : ℂ) (hα₀ : ((χD 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₀)
    (α₁ : ℂ) (hα₁ : ((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₁)
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (hfD : fD ∈ principalSeries2 v χD)
    (hfDK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → fD (g * k) = fD g)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) (k : ℤ) (hk : 1 ≤ k) (hmeasY : MeasurableSet (yShell v k)) (n : ℤ) :
    dualCell hπ V ℓ χD fD w₀ k n s =
      ((((selfDualHaarAt ℚ v) (yShell v k)).toReal : ℝ) : ℂ) * ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
        (fD 1 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * (k : ℂ))) *
          (α₀ ^ (n + k) * (Ideal.absNorm v.asIdeal : ℂ) ^ (((n + k : ℤ) : ℂ) * s) *
            localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 ((Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ (n + k)))))))) := by
  have H := LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v
  have hmeasA : MeasurableSet (aShell v n) := H.1 n
  have hmassA : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (aShell v n) = (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1} := by
    rw [show aShell v n = {y : (v.adicCompletion ℚ)ˣ | Valued.v (y : v.adicCompletion ℚ) = WithZero.exp (-(n))} from rfl,
      (H.2.2.1 n).1, neg_zero, WithZero.exp_zero]
  unfold dualCell
  have hinner : ∀ y ∈ yShell v k,
      (∫ a in aShell v n, dualCellIntegrand hπ V ℓ χD fD w₀ s y a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) =
        (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (fD 1 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * (k : ℂ))) *
          (α₀ ^ (n + k) * (Ideal.absNorm v.asIdeal : ℂ) ^ (((n + k : ℤ) : ℂ) * s) *
            localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 ((Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ (n + k))))))) := by
    intro y hy
    rw [setIntegral_congr_fun hmeasA (fun a ha =>
      dualCellIntegrand_tail_eq hπ hϖ V hVdK ℓ χD hχDu α₀ hα₀ α₁ hα₁ fD hfD hfDK w₀ hw₀ s k hk n y hy a ha),
      setIntegral_const, measureReal_def, hmassA, Complex.real_smul]
  rw [setIntegral_congr_fun hmeasY hinner, setIntegral_const, measureReal_def, Complex.real_smul]

end Cell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1"

end Ws46.MidT2
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section
namespace Ws1
namespace Middle
namespace Cells

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem iotaGL_diagUnitGL2_mul_lowerUnipotent21 {K : Type*} [Field K] (e : Kˣ) (x : K) :
    iotaGL (diagUnitGL2 e) * (lowerUnipotent21 x : GL (Fin 3) K) =
      lowerUnipotent21 ((e : K)⁻¹ * x) * iotaGL (diagUnitGL2 e) := by
  apply Units.ext
  have he : (e : K) ≠ 0 := e.ne_zero
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, lowerUnipotent21_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem diagUnitGL2_comm_diagUnits2 {K : Type*} [Field K] (e a b : Kˣ) :
    diagUnitGL2 e * diagUnits2 a b = diagUnits2 a b * diagUnitGL2 e := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagUnitGL2, coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

set_option maxHeartbeats 6400000 in

theorem localZeta31_hasSum_shells {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (F : LocalGL3 v → ℂ)
    (hFK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, F (g * iotaGL k) = F g)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χ e = 1)
    (w : ℂ) (n : ℤ)
    (hint : letI := localBorel ℚ v
      Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
        F (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) *
          ((χ p.1 : ℂˣ) : ℂ) * ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1))
        (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))).prod (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    HasSum (fun m : ℤ => ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
        ((∫ x, F (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) ∂(selfDualHaarAt ℚ v)) *
          ((χ (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(w - 1))) ^ m))
      (localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) F χ w (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)))) := by
  letI := localBorel ℚ v
  have H := LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq v
  have hmeas := H.1
  have hmass := fun m => (H.2.2.1 m).1

  set Hf : (v.adicCompletion ℚ)ˣ → ℂ := fun a =>
    (∫ x, F (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) ∂(selfDualHaarAt ℚ v)) *
      ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1) with hHf
  have hHint : Integrable Hf (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    have h1 := hint.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall fun a => ?_)
    show (∫ x, F (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1) ∂(selfDualHaarAt ℚ v)) = Hf a
    rw [hHf, integral_mul_const, integral_mul_const]
  have hsum := H.2.2.2.2 Hf hHint
  have hZdef : localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) F χ w (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) = ∫ a, Hf a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    simp only [localZeta31, hHf]
  rw [hZdef]

  have hcell : ∀ m : ℤ, (∫ a in {y : (v.adicCompletion ℚ)ˣ | Valued.v (y : v.adicCompletion ℚ) = WithZero.exp (-(m))}, Hf a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) =
      ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
        ((∫ x, F (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) ∂(selfDualHaarAt ℚ v)) *
          ((χ (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(w - 1))) ^ m) := by
    intro m
    have hconst : ∀ a ∈ {y : (v.adicCompletion ℚ)ˣ | Valued.v (y : v.adicCompletion ℚ) = WithZero.exp (-(m))},
        Hf a = (∫ x, F (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) ∂(selfDualHaarAt ℚ v)) *
          ((χ (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(w - 1))) ^ m := by
      intro a ha
      obtain ⟨e, he, hae⟩ := exists_unit_of_mem_aShell hπ hϖ m a ha
      have he0 : ((e : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≠ 0 := e.ne_zero
      have hmem : diagUnitGL2 e ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
        rw [← diagUnits2_one_right]
        have he' : Valued.v (((e⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀, he, inv_one]
        refine Ws1.Middle.DualD23.mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
        · rw [coe_diagUnits2]; fin_cases i <;> fin_cases j <;> simp [he]
        · have : (((diagUnits2 e (1 : (v.adicCompletion ℚ)ˣ))⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
              !![((e⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 0; 0, 1] := rfl
          rw [this]; fin_cases i <;> fin_cases j <;> simp [he]
      have hinner : (∫ x, F (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) ∂(selfDualHaarAt ℚ v)) =
          ∫ x, F (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) ∂(selfDualHaarAt ℚ v) := by
        have hpt : ∀ x, iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) =
            iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) * lowerUnipotent21 ((e : v.adicCompletion ℚ)⁻¹ * x) * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) *
              iotaGL (diagUnitGL2 e) := by
          intro x
          rw [hae, diagUnitGL2_mul, map_mul, mul_assoc (iotaGL _), iotaGL_diagUnitGL2_mul_lowerUnipotent21,
            ← mul_assoc, mul_assoc _ (iotaGL (diagUnitGL2 e)), ← map_mul, diagUnitGL2_comm_diagUnits2, map_mul,
            ← mul_assoc]
        simp_rw [hpt, hFK _ hmem]
        have := Ws46.MidT2.integral_comp_mul_left v
          (fun x => F (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)))) ((e : v.adicCompletion ℚ)⁻¹)
          (inv_ne_zero he0)
        rw [this, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, nnnorm_inv]
        have : ‖((e : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖₊ = 1 := by
          have hn : ‖((e : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ = 1 := by
            rw [NumberField.FinitePlace.norm_def]
            have h1 : (1 : ℝ) = ((1 : NNReal) : ℝ) := rfl
            rw [h1, NNReal.coe_inj, WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
              (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v))]
            exact he
          ext; rw [coe_nnnorm, hn]; rfl
        rw [this]; simp
      rw [hHf]
      show (∫ x, F (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) ∂(selfDualHaarAt ℚ v)) * ((χ a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (w - 1) = _
      rw [hinner, unramified_apply_of_mem_aShell hπ hϖ χ hχ m a ha, modulus_cpow_of_mem_aShell' (v := v) m a ha (w - 1)]
    rw [setIntegral_congr_fun (hmeas m) hconst, setIntegral_const, measureReal_def, hmass m, Complex.real_smul,
      neg_zero, WithZero.exp_zero]
  have hfun : (fun m : ℤ => ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
        ((∫ x, F (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ m)) * lowerUnipotent21 x * iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) ∂(selfDualHaarAt ℚ v)) *
          ((χ (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(w - 1))) ^ m)) =
      fun m : ℤ => ∫ a in {y : (v.adicCompletion ℚ)ˣ | Valued.v (y : v.adicCompletion ℚ) = WithZero.exp (-(m))}, Hf a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    funext m; rw [hcell m]
  rw [hfun]
  exact hsum

end Ws1.Middle.Cells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal
open scoped ENNReal NNReal

noncomputable section

namespace Ws1
namespace Middle
namespace ShellMass

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => HeightOneSpectrum.adicCompletion ℚ v

theorem one_lt_qR : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem qR_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one (one_lt_qR v)

theorem norm_eq_of_valued_eq_exp {m : ℤ} {a : Fv} (ha : Valued.v a = WithZero.exp m) :
    ‖a‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, ha, WithZero.exp,
    WithZeroMulInt.toNNReal_neg_apply _ (WithZero.coe_ne_zero), WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow]
  rfl

theorem valued_eq_exp_log {a : Fv} (ha : a ≠ 0) : Valued.v a = WithZero.exp (WithZero.log (Valued.v a)) :=
  (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr ha)).symm

theorem setOf_valued_le_exp_eq (n : ℤ) :
    {y : Fv | Valued.v y ≤ WithZero.exp n} = Metric.closedBall (0 : Fv) ((Ideal.absNorm v.asIdeal : ℝ) ^ n) := by
  ext y
  simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  by_cases hy : y = 0
  · subst hy
    simp [(zpow_pos (qR_pos v) n).le]
  · have hv := valued_eq_exp_log v hy
    rw [norm_eq_of_valued_eq_exp v hv, hv, WithZero.exp_le_exp, zpow_le_zpow_iff_right₀ (one_lt_qR v),
      WithZero.log_exp]

theorem measurableSet_valued_le_exp (n : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet {y : Fv | Valued.v y ≤ WithZero.exp n} := by
  letI := localBorel ℚ v
  haveI : BorelSpace Fv := ⟨rfl⟩
  rw [setOf_valued_le_exp_eq]
  exact Metric.isClosed_closedBall.measurableSet

theorem setOf_valued_eq_exp_eq_sdiff (n : ℤ) :
    {y : Fv | Valued.v y = WithZero.exp n} =
      {y : Fv | Valued.v y ≤ WithZero.exp n} \ {y : Fv | Valued.v y ≤ WithZero.exp (n - 1)} := by
  ext y
  simp only [Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨h.le, fun h' => ?_⟩
    rw [h, WithZero.exp_le_exp] at h'
    omega
  · rintro ⟨h1, h2⟩
    have hy : y ≠ 0 := by
      rintro rfl
      exact h2 (by simp)
    have hv := valued_eq_exp_log v hy
    rw [hv] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    rw [(WithZero.exp_injective).eq_iff]
    omega

theorem measureReal_sphere (n : ℤ) :
    letI := localBorel ℚ v
    ∀ (ν : Measure Fv) [ν.IsAddHaarMeasure],
      (ν {y : Fv | Valued.v y = WithZero.exp n}).toReal =
        ((Ideal.absNorm v.asIdeal : ℝ) ^ n - (Ideal.absNorm v.asIdeal : ℝ) ^ (n - 1)) *
          (ν {y : Fv | Valued.v y ≤ 1}).toReal := by
  letI := localBorel ℚ v
  intro ν _
  obtain ⟨hball, -⟩ := LanglandsTunnell.TateLocal.addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat v ν
  obtain ⟨-, hfin, hn⟩ := hball n
  obtain ⟨-, hfin', hn'⟩ := hball (n - 1)
  have hsub : {y : Fv | Valued.v y ≤ WithZero.exp (n - 1)} ⊆ {y : Fv | Valued.v y ≤ WithZero.exp n} := by
    intro y hy
    exact le_trans hy (WithZero.exp_le_exp.2 (by omega))
  rw [setOf_valued_eq_exp_eq_sdiff, measure_diff hsub (measurableSet_valued_le_exp v (n - 1)).nullMeasurableSet
    hfin'.ne, ENNReal.toReal_sub_of_le (measure_mono hsub) hfin.ne, hn, hn']
  ring

theorem shellMass_succ :
    letI := localBorel ℚ v
    ∀ (ν : Measure Fv) [ν.IsAddHaarMeasure] (k : ℕ),
      (((ν {y : Fv | Valued.v y = WithZero.exp (((k + 1 : ℕ) : ℤ))}).toReal : ℝ) : ℂ) =
        (((ν {y : Fv | Valued.v y ≤ 1}).toReal : ℝ) : ℂ) *
          ((Ideal.absNorm v.asIdeal : ℂ) ^ (k + 1) - (Ideal.absNorm v.asIdeal : ℂ) ^ k) := by
  letI := localBorel ℚ v
  intro ν _ k
  rw [measureReal_sphere v (((k + 1 : ℕ) : ℤ)) ν]
  push_cast
  rw [show ((k : ℤ) + 1 - 1) = (k : ℤ) by ring, zpow_natCast,
    show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  ring

theorem range_units_val : Set.range (Units.val : (Fv)ˣ → Fv) = {x : Fv | x ≠ 0} := by
  ext x
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩

theorem measurableSet_image_units_val :
    letI := localBorel ℚ v
    ∀ s : Set (Fv)ˣ, MeasurableSet s → MeasurableSet (Units.val '' s) := by
  letI := localBorel ℚ v
  haveI : BorelSpace Fv := ⟨rfl⟩
  intro s hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  rw [Set.image_preimage_eq_inter_range, range_units_val]
  exact ht.inter (measurableSet_singleton (0 : Fv)).compl

theorem image_units_val_sphere_one :
    Units.val '' {u : (Fv)ˣ | Valued.v (u : Fv) = 1} = {x : Fv | Valued.v x = WithZero.exp (0 : ℤ)} := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, WithZero.exp_zero]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    exact ⟨Units.mk0 x hx0, hx, rfl⟩

theorem mulMeasure_unitSphere :
    letI := localBorel ℚ v
    ∀ (ν : Measure Fv) [ν.IsAddHaarMeasure],
      ((Measure.comap Units.val (mulMeasure ν)) {u : (Fv)ˣ | Valued.v (u : Fv) = 1}).toReal =
        (1 - ((Ideal.absNorm v.asIdeal : ℝ))⁻¹) * (ν {y : Fv | Valued.v y ≤ 1}).toReal := by
  letI := localBorel ℚ v
  haveI : BorelSpace Fv := ⟨rfl⟩
  intro ν _
  have hT : MeasurableSet {x : Fv | Valued.v x = WithZero.exp (0 : ℤ)} := by
    rw [setOf_valued_eq_exp_eq_sdiff]
    exact (measurableSet_valued_le_exp v 0).diff (measurableSet_valued_le_exp v (0 - 1))
  have hS : MeasurableSet {u : (Fv)ˣ | Valued.v (u : Fv) = 1} := by
    refine MeasurableSpace.measurableSet_comap.2 ⟨{x : Fv | Valued.v x = WithZero.exp (0 : ℤ)}, hT, ?_⟩
    ext u; simp
  rw [Measure.comap_apply Units.val (fun a b h => Units.ext h) (measurableSet_image_units_val v) _ hS,
    image_units_val_sphere_one]

  have h0 : {x : Fv | Valued.v x = WithZero.exp (0 : ℤ)} ∩ {0}ᶜ = {x : Fv | Valued.v x = WithZero.exp (0 : ℤ)} := by
    refine Set.inter_eq_left.2 fun x hx h0 => ?_
    rw [Set.mem_singleton_iff] at h0
    rw [h0, Set.mem_setOf_eq, map_zero] at hx
    exact WithZero.zero_ne_coe hx
  have hdens : Set.EqOn (fun x : Fv => ((modulus x : ℝ≥0) : ℝ≥0∞)⁻¹) (fun _ => 1)
      {x : Fv | Valued.v x = WithZero.exp (0 : ℤ)} := by
    intro x hx
    have hn : ‖x‖ = 1 := by rw [norm_eq_of_valued_eq_exp v hx, zpow_zero]
    have : modulus x = 1 := by
      rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x]
      ext; rw [coe_nnnorm, hn]; rfl
    simp [this]
  unfold mulMeasure
  rw [withDensity_apply _ hT, Measure.restrict_restrict hT, h0, setLIntegral_congr_fun hT hdens, setLIntegral_one,
    measureReal_sphere v 0 ν, zpow_zero, show (0 : ℤ) - 1 = -1 by ring, zpow_neg_one]

theorem mulMeasure_unitSphere_complex :
    letI := localBorel ℚ v
    ∀ (ν : Measure Fv) [ν.IsAddHaarMeasure],
      ((((Measure.comap Units.val (mulMeasure ν)) {u : (Fv)ˣ | Valued.v (u : Fv) = 1}).toReal : ℝ) : ℂ) =
        (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * (((ν {y : Fv | Valued.v y ≤ 1}).toReal : ℝ) : ℂ) := by
  letI := localBorel ℚ v
  intro ν _
  rw [mulMeasure_unitSphere v ν]
  push_cast
  ring

end Ws1.Middle.ShellMass
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal NumberField.TateGlobal NumberField.StandardAddChar
open scoped ENNReal NNReal

noncomputable section
namespace Ws1
namespace Middle
namespace SelfDualMass

theorem selfDualHaarAt_real_integers_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} = 1 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ 1} =
      (integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ)) := by
    rw [coe_integersPositiveCompacts]; ext x
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) ℚ v (x := x)).symm
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal ℚ v) : ℝ) / 2) with hc
  have hdef : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  have hc1 : c = 1 := by rw [hc, addCharLevel_psiLocal_rat]; simp
  rw [Measure.real, hset, hdef, Measure.smul_apply, Measure.addHaarMeasure_self, hc1]
  simp

end Ws1.Middle.SelfDualMass
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

open Finset

namespace Ws1
namespace Middle
namespace DualGlue

theorem summable_norm_L {cell : ℤ → ℤ → ℂ} {L : ℤ → ℂ} {νS : ℤ → ℂ}
    (hT1 : Summable fun p : ℤ × ℤ => ‖cell p.1 p.2‖)
    (hbulk : ∀ k : ℤ, k ≤ 0 → ∀ n : ℤ, cell k n = νS k * L n) (hν0 : νS 0 ≠ 0) :
    Summable fun n : ℤ => ‖L n‖ := by
  have hinj : Function.Injective (fun n : ℤ => ((0 : ℤ), n)) := fun a b h => (Prod.ext_iff.mp h).2
  have h0 : Summable fun n : ℤ => ‖cell 0 n‖ := by
    have h := hT1.comp_injective hinj
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
  have h1 : Summable fun n : ℤ => ‖νS 0‖⁻¹ * ‖cell 0 n‖ := h0.mul_left _
  refine h1.congr fun n => ?_
  rw [hbulk 0 le_rfl n, norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hν0), one_mul]

theorem summable_L {cell : ℤ → ℤ → ℂ} {L : ℤ → ℂ} {νS : ℤ → ℂ}
    (hT1 : Summable fun p : ℤ × ℤ => ‖cell p.1 p.2‖)
    (hbulk : ∀ k : ℤ, k ≤ 0 → ∀ n : ℤ, cell k n = νS k * L n) (hν0 : νS 0 ≠ 0) :
    Summable L :=
  (summable_norm_L hT1 hbulk hν0).of_norm

theorem hasSum_geometric_tail {θ : ℂ} (hθ : ‖θ‖ < 1) :
    HasSum (fun k : ℕ => θ ^ (k + 1)) (θ / (1 - θ)) := by
  have h := (hasSum_geometric_of_norm_lt_one hθ).mul_left θ
  simp only [← pow_succ'] at h
  rwa [div_eq_mul_inv]

theorem tsum_weights (νS : ℤ → ℂ) (q μ₀ μ₁ : ℂ) (hq : q ≠ 0) (hq1 : ‖q⁻¹‖ < 1)
    (hF1 : HasSum (fun j : ℕ => νS (-(j : ℤ))) μ₀)
    (hF2 : ∀ k : ℤ, 1 ≤ k → νS k = μ₁ * q ^ k) (hμ₁ : μ₁ = μ₀ * (1 - q⁻¹)) :
    HasSum (fun k : ℤ => if k ≤ 0 then νS k else νS k * q ^ (-2 * k)) (μ₀ * (1 + q⁻¹)) := by
  set w : ℤ → ℂ := fun k => if k ≤ 0 then νS k else νS k * q ^ (-2 * k) with hw

  have hnat : HasSum (fun n : ℕ => w (-(n : ℤ))) μ₀ := by
    refine hF1.congr_fun fun n => ?_
    simp only [hw]
    rw [if_pos (by omega)]
  have hneg : HasSum (fun n : ℕ => w (-(-((n : ℤ) + 1)))) (μ₁ * (q⁻¹ / (1 - q⁻¹))) := by
    have hg := (hasSum_geometric_tail hq1).mul_left μ₁
    refine hg.congr_fun fun n => ?_
    simp only [hw, neg_neg]
    rw [if_neg (by omega), hF2 _ (by omega), mul_assoc, ← zpow_add₀ hq,
      show (n : ℤ) + 1 + -2 * ((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
  have hw' : HasSum (fun k : ℤ => w (-k)) (μ₀ + μ₁ * (q⁻¹ / (1 - q⁻¹))) :=
    HasSum.of_nat_of_neg_add_one hnat hneg
  have hw'' : HasSum w (μ₀ + μ₁ * (q⁻¹ / (1 - q⁻¹))) := by
    refine ((Equiv.neg ℤ).hasSum_iff).mp ?_
    refine hw'.congr_fun fun k => ?_
    simp only [Function.comp_apply, Equiv.neg_apply]
  have h1 : (1 : ℂ) - q⁻¹ ≠ 0 := by
    intro h
    have : q⁻¹ = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at hq1
    exact lt_irrefl _ hq1
  have hqne1 : q ≠ 1 := fun h => by
    rw [h, inv_one, norm_one] at hq1
    exact lt_irrefl _ hq1
  have hqm1 : -1 + q ≠ 0 := by rw [neg_add_eq_sub]; exact sub_ne_zero.mpr hqne1
  have hqm1' : q - 1 ≠ 0 := sub_ne_zero.mpr hqne1
  have heq : μ₀ + μ₁ * (q⁻¹ / (1 - q⁻¹)) = μ₀ * (1 + q⁻¹) := by
    rw [hμ₁]
    field_simp
  rw [heq] at hw''
  exact hw''

theorem lattice_sum_identity
    (cell : ℤ → ℤ → ℂ) (L : ℤ → ℂ) (νS : ℤ → ℂ) (q μ₀ μ₁ K X Y Ed₁ D₁X D₂Y : ℂ)
    (hq : q ≠ 0) (hq1 : ‖q⁻¹‖ < 1) (hY : Y ≠ 0)
    (N₀ : ℤ) (row : ℕ → Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ)
    (hT1 : Summable fun p : ℤ × ℤ => ‖cell p.1 p.2‖)
    (hbulk : ∀ k : ℤ, k ≤ 0 → ∀ n : ℤ, cell k n = νS k * L n)
    (htail : ∀ k : ℤ, 1 ≤ k → ∀ n : ℤ, cell k n = νS k * q ^ (-2 * k) * L (n + k))
    (hν0 : νS 0 ≠ 0)
    (hF1 : HasSum (fun j : ℕ => νS (-(j : ℤ))) μ₀)
    (hF2 : ∀ k : ℤ, 1 ≤ k → νS k = μ₁ * q ^ k)
    (hμ₁ : μ₁ = μ₀ * (1 - q⁻¹))
    (hcore : ∀ n : ℤ, N₀ ≤ n → L n * Ed₁ * D₁X = K * Y ^ n * (row (n - N₀).toNat).eval X)
    (hcore₀ : ∀ n : ℤ, n < N₀ → L n = 0)
    (hresum : Summable (fun j : ℕ => ‖(row j).eval X * Y ^ j‖) ∧
      (∑' j : ℕ, (row j).eval X * Y ^ j) * D₂Y = MvPolynomial.eval ![X, Y] P) :
    (∑' p : ℤ × ℤ, cell p.1 p.2) * Ed₁ * D₁X * D₂Y = μ₀ * (1 + q⁻¹) * K * Y ^ N₀ * MvPolynomial.eval ![X, Y] P := by
  have hL : Summable L := summable_L hT1 hbulk hν0
  set SL : ℂ := ∑' n : ℤ, L n with hSL

  have hsum : Summable (fun p : ℤ × ℤ => cell p.1 p.2) := hT1.of_norm
  have hslice : ∀ k : ℤ, Summable fun n : ℤ => cell k n := fun k => by
    have h := hT1.comp_injective (show Function.Injective (fun n : ℤ => (k, n)) from
      fun a b h => (Prod.ext_iff.mp h).2)
    exact (h.congr fun n => by simp only [Function.comp_apply]).of_norm
  have h1 : ∑' p : ℤ × ℤ, cell p.1 p.2 = ∑' k : ℤ, ∑' n : ℤ, cell k n :=
    hsum.tsum_prod' hslice

  set w : ℤ → ℂ := fun k => if k ≤ 0 then νS k else νS k * q ^ (-2 * k) with hw
  have h2 : ∀ k : ℤ, ∑' n : ℤ, cell k n = w k * SL := by
    intro k
    by_cases hk : k ≤ 0
    · simp only [hw, if_pos hk]
      rw [show (fun n : ℤ => cell k n) = fun n => νS k * L n from funext (hbulk k hk), tsum_mul_left]
    · simp only [hw, if_neg hk]
      have hk1 : 1 ≤ k := by omega
      rw [show (fun n : ℤ => cell k n) = fun n => (νS k * q ^ (-2 * k)) * L (n + k) from funext (htail k hk1),
        tsum_mul_left]
      congr 1
      exact (Equiv.addRight k).tsum_eq L
  have h3 : ∑' k : ℤ, ∑' n : ℤ, cell k n = (μ₀ * (1 + q⁻¹)) * SL := by
    rw [show (fun k : ℤ => ∑' n : ℤ, cell k n) = fun k => w k * SL from funext h2, tsum_mul_right,
      (tsum_weights νS q μ₀ μ₁ hq hq1 hF1 hF2 hμ₁).tsum_eq]

  have h4 : SL * (Ed₁ * D₁X) = K * Y ^ N₀ * ∑' j : ℕ, (row j).eval X * Y ^ j := by
    rw [hSL, ← tsum_mul_right]
    set M : ℤ → ℂ := fun n => L n * (Ed₁ * D₁X) with hM
    set i : ℕ → ℤ := fun j => N₀ + (j : ℤ) with hi
    have hinj : Function.Injective i := fun a b h => by simp only [hi] at h; exact_mod_cast (add_left_cancel h)
    have hsupp : Function.support M ⊆ Set.range i := by
      intro n hn
      by_cases hn0 : N₀ ≤ n
      · exact ⟨(n - N₀).toNat, by simp only [hi]; omega⟩
      · exact absurd (by simp only [hM, Function.mem_support, ne_eq] at hn; rw [hcore₀ n (by omega)] at hn; simpa using hn) id
    rw [show (∑' n : ℤ, L n * (Ed₁ * D₁X)) = ∑' n, M n from rfl, ← hinj.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hM, hi]
    rw [← mul_assoc, hcore _ (by omega), show (N₀ + (j : ℤ) - N₀).toNat = j by omega, zpow_add₀ hY, zpow_natCast]
    ring

  calc (∑' p : ℤ × ℤ, cell p.1 p.2) * Ed₁ * D₁X * D₂Y
      = (μ₀ * (1 + q⁻¹)) * (SL * (Ed₁ * D₁X)) * D₂Y := by rw [h1, h3]; ring
    _ = (μ₀ * (1 + q⁻¹)) * (K * Y ^ N₀) * ((∑' j : ℕ, (row j).eval X * Y ^ j) * D₂Y) := by rw [h4]; ring
    _ = μ₀ * (1 + q⁻¹) * K * Y ^ N₀ * MvPolynomial.eval ![X, Y] P := by rw [hresum.2]; ring

end Ws1.Middle.DualGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace Ws1
namespace Middle
namespace DualGlue

open scoped ENNReal NNReal

section Merge

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev Fv : Type := v.adicCompletion ℚ

abbrev G2 : Type := GL (Fin 2) (v.adicCompletion ℚ)

abbrev K2 : Subgroup (G2 v) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤

theorem isLocalLevelOne_top_of_integral {m : Matrix (Fin 2) (Fin 2) (Fv v)}
    (h : ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : Fv v)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_K2_iff (k : G2 v) :
    k ∈ K2 v ↔ (∀ i j, (k : Matrix (Fin 2) (Fin 2) (Fv v)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      ∀ i j, ((k⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) i j ∈ v.adicCompletionIntegers ℚ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral v h1, isLocalLevelOne_top_of_integral v h2⟩

private theorem _root_.Ws1.Middle.DualGlue.mem_K2_of_entries {k : G2 v}
    (h : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((k⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1) : k ∈ K2 v :=
  (mem_K2_iff v k).mpr ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h i j),
    fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h' i j)⟩

p2m_export "Ws1.Middle.DualGlue" "mem_K2_of_entries"

def lowerUnipotentGL2 (x : Fv v) : G2 v :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_lowerUnipotentGL2 (x : Fv v) :
    ((lowerUnipotentGL2 v x : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; x, 1] := rfl

theorem coe_inv_lowerUnipotentGL2 (x : Fv v) :
    (((lowerUnipotentGL2 v x)⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; -x, 1] := rfl

theorem coe_inv_unipotentGL2 (x : Fv v) :
    (((unipotentGL2 x : G2 v)⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, -x; 0, 1] := rfl

private theorem _root_.Ws1.Middle.DualGlue.unipotentGL2_mem_K2 {y : Fv v} (hy : Valued.v y ≤ 1) : (unipotentGL2 y : G2 v) ∈ K2 v := by
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [coe_inv_unipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hy, Valuation.map_neg]

p2m_export "Ws1.Middle.DualGlue" "unipotentGL2_mem_K2"
theorem lowerUnipotentGL2_mem_K2 {x : Fv v} (hx : Valued.v x ≤ 1) : lowerUnipotentGL2 v x ∈ K2 v := by
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [coe_lowerUnipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [coe_inv_lowerUnipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hx, Valuation.map_neg]

private theorem _root_.Ws1.Middle.DualGlue.w0_mem_K2 {w₀ : G2 v} (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0]) : w₀ ∈ K2 v := by
  have hinv : ((w₀⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0] := by
    rw [Matrix.coe_units_inv, hw₀]
    refine Matrix.inv_eq_left_inv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [hw₀]; fin_cases i <;> fin_cases j <;> simp
  · rw [hinv]; fin_cases i <;> fin_cases j <;> simp

p2m_export "Ws1.Middle.DualGlue" "w0_mem_K2"

def w0 : G2 v :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_w0 : ((w0 v : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0] := rfl

theorem weylPrime3_mul_iotaGL_w0 : (weylPrime3 : LocalGL3 v) * iotaGL (w0 v) = longWeyl3 * weylPrime3 := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, coe_w0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, longWeyl3, weylPrime3, Matrix.mul_apply, Fin.sum_univ_three]

theorem scalarPi_mul_comm {ϖ : v.adicCompletionIntegers ℚ} (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0) (g : G2 v) :
    scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ * g = g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ := by
  apply Units.ext
  simp only [Units.val_mul, UnramifiedWhittaker.scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem merge (V : LocalGL3 v → ℂ) (hVK : ∀ k ∈ K2 v, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g) :
    (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3))) = fun x : LocalGL3 v => V (x * weylPrime3) := by
  funext x
  rw [← weylPrime3_mul_iotaGL_w0, ← mul_assoc, hVK _ (w0_mem_K2 v (coe_w0 v))]

theorem mergeL (V : LocalGL3 v → ℂ) (hVK : ∀ k ∈ K2 v, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    {ϖ : v.adicCompletionIntegers ℚ} (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0) (ℓ : ℤ) :
    (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3 * iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ ℓ)))) =
      fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ ℓ))) := by
  funext x
  have hc : iotaGL (w0 v) * iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ ℓ) =
      iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ ℓ) * (iotaGL (w0 v) : LocalGL3 v) := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact ((Commute.symm (scalarPi_mul_comm v hπ (w0 v))).zpow_right ℓ).eq
  rw [← weylPrime3_mul_iotaGL_w0, mul_assoc (weylPrime3 : LocalGL3 v), hc, ← mul_assoc (weylPrime3 : LocalGL3 v),
    ← mul_assoc x, hVK _ (w0_mem_K2 v (coe_w0 v))]

theorem numDen_eq {ϖ : v.adicCompletionIntegers ℚ} (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0)
    (V : LocalGL3 v → ℂ) (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (ℓ : ℕ)
    (N₀ : ℤ) (D₀₁ D₀₂ : Polynomial ℂ) (P₀ : MvPolynomial (Fin 2) ℂ) (r₀ : ℝ)
    (hTD₀ : IsTorusDatum v hπ
      (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ)))))
      N₀ D₀₁ D₀₂ P₀ r₀)
    (Nt : ℤ) (Dt₁ Dt₂ : Polynomial ℂ) (Pt : MvPolynomial (Fin 2) ℂ) (rt : ℝ)
    (hTDt : IsTorusDatum v hπ
      (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ)))))
      Nt Dt₁ Dt₂ Pt rt)
    (X Y : ℂ) (hX : X ≠ 0) (hY : Y ≠ 0) :
    torusNum Nt Pt X Y * torusDen D₀₁ D₀₂ X Y = torusNum N₀ P₀ X Y * torusDen Dt₁ Dt₂ X Y := by
  rw [mergeL v V hVK hπ (ℓ : ℤ)] at hTDt
  exact (torusDatum_unique v hπ _ N₀ D₀₁ D₀₂ P₀ r₀ Nt Dt₁ Dt₂ Pt rt hTD₀ hTDt X Y hX hY).symm

end Merge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section Radii

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem dualX_ne_zero (α₁ : ℂ) (hα₁ : α₁ ≠ 0) (s : ℂ) : dualX v α₁ s ≠ 0 := by
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  unfold dualX
  exact mul_ne_zero (inv_ne_zero hα₁) (fun h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1)

theorem dualY_ne_zero (α₀ ω : ℂ) (hα₀ : α₀ ≠ 0) (hω : ω ≠ 0) (s : ℂ) : dualY v α₀ ω s ≠ 0 := by
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  unfold dualY
  exact mul_ne_zero (mul_ne_zero hα₀ (inv_ne_zero hω)) (fun h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1)

theorem dualAlpha0_ne_zero (a : ℂ) (ha : a ≠ 0) : dualAlpha0 v a ≠ 0 := by
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  unfold dualAlpha0
  exact mul_ne_zero (fun h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1) (inv_ne_zero ha)

theorem dualAlpha1_ne_zero (a : ℂ) (ha : a ≠ 0) : dualAlpha1 v a ≠ 0 := by
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  unfold dualAlpha1
  exact mul_ne_zero (fun h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1) (inv_ne_zero ha)

theorem exists_forall_norm_dualY_lt (α₀ ω : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < (1 - s).re → ‖dualY v α₀ ω s‖ < r := by
  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one hN
  set c : ℝ := ‖α₀ * ω⁻¹‖ + 1 with hc
  have hc0 : 0 < c := by rw [hc]; linarith [norm_nonneg (α₀ * ω⁻¹)]
  have hlt : ‖α₀ * ω⁻¹‖ < c := by rw [hc]; linarith
  obtain ⟨σ₀, hσ₀⟩ := Filter.eventually_atTop.mp
    ((Ws1.Middle.Laurent1.tendsto_rpow_neg hq).eventually (gt_mem_nhds (div_pos hr (mul_pos hc0 hN0))))
  refine ⟨σ₀, fun s hs => ?_⟩
  unfold dualY
  rw [norm_mul, Ws1.Middle.Laurent1.norm_cpow hq]

  have hre : s.re = 1 - (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; ring
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ s.re < (Ideal.absNorm v.asIdeal : ℝ) * (r / (c * (Ideal.absNorm v.asIdeal : ℝ))) := by
    rw [hre, show (1 : ℝ) - (1 - s).re = 1 + (-(1 - s).re) by ring, Real.rpow_add hN0, Real.rpow_one]
    refine mul_lt_mul_of_pos_left ?_ hN0
    exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)) (hσ₀ σ₀ le_rfl)
  have h2 : (Ideal.absNorm v.asIdeal : ℝ) * (r / (c * (Ideal.absNorm v.asIdeal : ℝ))) = r / c := by
    field_simp
  rw [h2] at h1
  calc ‖α₀ * ω⁻¹‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ s.re ≤ c * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ s.re :=
        mul_le_mul_of_nonneg_right hlt.le (Real.rpow_nonneg hN0.le _)
    _ < c * (r / c) := mul_lt_mul_of_pos_left h1 hc0
    _ = r := by field_simp

end Radii
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section Tail

theorem htail_of_tail_eq (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0) (V : LocalGL3 v → ℂ) (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (α₀ : ℂ) (s : ℂ)
    (h46 : letI := localBorel ℚ v
      ∀ k : ℤ, 1 ≤ k → ∀ n : ℤ, Ws1.Middle.Cells.dualCell hπ V ℓ χD fD w₀ k n s =
        ((((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v (k))).toReal : ℝ) : ℂ) * ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) *
          (fD 1 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * (k : ℂ))) *
            (α₀ ^ (n + k) * (Ideal.absNorm v.asIdeal : ℂ) ^ (((n + k : ℤ) : ℂ) * s) * localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 ((Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) ^ (n + k))))))))) :
    letI := localBorel ℚ v
    ∀ k : ℤ, 1 ≤ k → ∀ n : ℤ, Ws1.Middle.Cells.dualCell hπ V ℓ χD fD w₀ k n s =
      ((((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v (k))).toReal : ℝ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-2 * k) *
        ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (fD 1 * (α₀ ^ (n + k) * (Ideal.absNorm v.asIdeal : ℂ) ^ (((n + k : ℤ) : ℂ) * s) * localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n + k))))))) := by
  letI := localBorel ℚ v
  intro k hk n
  rw [h46 k hk n, show (-(2 * (k : ℂ))) = ((-2 * k : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  ring

end Tail
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

end Ws1.Middle.DualGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace SlMID

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev Fv : Type := v.adicCompletion ℚ

abbrev G2 : Type := GL (Fin 2) (v.adicCompletion ℚ)

abbrev K2 : Subgroup (G2 v) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤

theorem isLocalLevelOne_top_of_integral {m : Matrix (Fin 2) (Fin 2) (Fv v)}
    (h : ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : Fv v)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_K2_iff (k : G2 v) :
    k ∈ K2 v ↔ (∀ i j, (k : Matrix (Fin 2) (Fin 2) (Fv v)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      ∀ i j, ((k⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) i j ∈ v.adicCompletionIntegers ℚ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral v h1, isLocalLevelOne_top_of_integral v h2⟩

private theorem _root_.SlMID.mem_K2_of_entries {k : G2 v}
    (h : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((k⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1) : k ∈ K2 v :=
  (mem_K2_iff v k).mpr ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h i j),
    fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h' i j)⟩

p2m_export "SlMID" "mem_K2_of_entries"

def lowerUnipotentGL2 (x : Fv v) : G2 v :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_lowerUnipotentGL2 (x : Fv v) :
    ((lowerUnipotentGL2 v x : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; x, 1] := rfl

theorem coe_inv_lowerUnipotentGL2 (x : Fv v) :
    (((lowerUnipotentGL2 v x)⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; -x, 1] := rfl

theorem coe_inv_unipotentGL2 (x : Fv v) :
    (((unipotentGL2 x : G2 v)⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, -x; 0, 1] := rfl

private theorem _root_.SlMID.unipotentGL2_mem_K2 {y : Fv v} (hy : Valued.v y ≤ 1) : (unipotentGL2 y : G2 v) ∈ K2 v := by
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [coe_inv_unipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hy, Valuation.map_neg]

p2m_export "SlMID" "unipotentGL2_mem_K2"
theorem lowerUnipotentGL2_mem_K2 {x : Fv v} (hx : Valued.v x ≤ 1) : lowerUnipotentGL2 v x ∈ K2 v := by
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [coe_lowerUnipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [coe_inv_lowerUnipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hx, Valuation.map_neg]

private theorem _root_.SlMID.w0_mem_K2 {w₀ : G2 v} (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0]) : w₀ ∈ K2 v := by
  have hinv : ((w₀⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0] := by
    rw [Matrix.coe_units_inv, hw₀]
    refine Matrix.inv_eq_left_inv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [hw₀]; fin_cases i <;> fin_cases j <;> simp
  · rw [hinv]; fin_cases i <;> fin_cases j <;> simp

p2m_export "SlMID" "w0_mem_K2"

section Inst

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

scoped instance borelSpace_units_adic : BorelSpace (Fv v)ˣ := borelSpace_units

scoped instance secondCountable_units_adic : SecondCountableTopology (Fv v)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

private scoped instance _root_.SlMID.isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

p2m_export "SlMID" "isAddHaarMeasure_selfDualHaarAt"
scoped instance isHaarMeasure_mulHaar :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure (Fv v)ˣ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure ℚ v (selfDualHaarAt ℚ v)

theorem one_lt_q : 1 < Ideal.absNorm v.asIdeal := by
  refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot, ?_⟩
  exact Ideal.absNorm_eq_one_iff.not.mpr (Ideal.IsPrime.ne_top v.isPrime)

theorem one_lt_qR : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_q v

theorem qR_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one (one_lt_qR v)

theorem qC_ne_zero : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

theorem qC_eq : (Ideal.absNorm v.asIdeal : ℂ) = ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) := by norm_cast

theorem norm_qC_cpow (S : ℂ) :
    ‖(Ideal.absNorm v.asIdeal : ℂ) ^ S‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ S.re := by
  rw [qC_eq, Complex.norm_cpow_eq_rpow_re_of_pos (qR_pos v)]

end Inst
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section Cyc

variable {v} {W₃ : LocalGL3 v → ℂ}

private theorem _root_.SlMID.law_of_mem_gl3CyclicSubspace {θ : AddChar (Fv v) ℂ}
    (hW₃law : IsGL3PsiWhittakerFn θ W₃) {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    IsGL3PsiWhittakerFn θ W := by
  have hle : gl3CyclicSubspace W₃ ≤ gl3PsiWhittakerFnSpace (Fv v) ℂ θ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace θ h ((mem_gl3PsiWhittakerFnSpace_iff θ _).mpr hW₃law)
  exact (mem_gl3PsiWhittakerFnSpace_iff θ _).mp (hle hW)

p2m_export "SlMID" "law_of_mem_gl3CyclicSubspace"
private theorem _root_.SlMID.central_of_mem_gl3CyclicSubspace {ω : (Fv v)ˣ →* ℂˣ}
    (hω : ∀ (z : (Fv v)ˣ) (g : LocalGL3 v),
      W₃ (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W₃ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    ∀ (z : (Fv v)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g := by
  refine Submodule.span_induction (p := fun W _ => ∀ (z : (Fv v)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ z g
    simp only [gl3AmbientRightTranslate_apply]
    rw [mul_assoc, hω]
  · intro z g; simp
  · intro f g _ _ hf hg z x
    simp only [Pi.add_apply]
    rw [hf, hg]; ring
  · intro a f _ hf z x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]; ring

p2m_export "SlMID" "central_of_mem_gl3CyclicSubspace"
private theorem _root_.SlMID.smooth_of_mem_gl3CyclicSubspace
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
      W₃ (g * k) = W₃ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
      W (g * k) = W g := by
  refine Submodule.span_induction (p := fun W _ =>
      ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
        W (g * k) = W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩
    obtain ⟨Uv, hUv, hinv⟩ := hW₃sm
    let φ : LocalGL3 v →* LocalGL3 v := (MulAut.conj h⁻¹).toMonoidHom
    refine ⟨Uv.comap φ, ?_, ?_⟩
    · have hφ : Continuous φ := by
        change Continuous fun x : LocalGL3 v => h⁻¹ * x * h⁻¹⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const
      exact hUv.preimage hφ
    · intro k hk g
      have hk' : h⁻¹ * k * h ∈ Uv := by
        have := hk
        rw [Subgroup.mem_comap] at this
        simpa [φ] using this
      simp only [gl3AmbientRightTranslate_apply]
      have : g * k * h = g * h * (h⁻¹ * k * h) := by group
      rw [this, hinv _ hk']
  · obtain ⟨Uv, hUv, _⟩ := hW₃sm
    exact ⟨Uv, hUv, fun k _ g => rfl⟩
  · rintro f g _ _ ⟨U₁, hU₁, h₁⟩ ⟨U₂, hU₂, h₂⟩
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk x => ?_⟩
    · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
    · simp only [Pi.add_apply]
      rw [h₁ k (Subgroup.mem_inf.mp hk).1, h₂ k (Subgroup.mem_inf.mp hk).2]
  · rintro a f _ ⟨U, hU, h⟩
    exact ⟨U, hU, fun k hk x => by simp only [Pi.smul_apply, smul_eq_mul]; rw [h k hk]⟩

p2m_export "SlMID" "smooth_of_mem_gl3CyclicSubspace"
end Cyc
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

def ordU (u : (Fv v)ˣ) : ℤ := -WithZero.log (Valued.v (u : Fv v))

theorem valued_eq_exp_neg_ordU (u : (Fv v)ˣ) : Valued.v (u : Fv v) = WithZero.exp (-ordU v u) := by
  rw [ordU, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr u.ne_zero)]

theorem ordU_mul (a b : (Fv v)ˣ) : ordU v (a * b) = ordU v a + ordU v b := by
  simp only [ordU, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr a.ne_zero) ((Valuation.ne_zero_iff _).mpr b.ne_zero)]
  ring

theorem ordU_one : ordU v 1 = 0 := by simp [ordU]

theorem ordU_eq_zero_of_valued_eq_one {u : (Fv v)ˣ} (hu : Valued.v (u : Fv v) = 1) : ordU v u = 0 := by
  simp [ordU, hu]

theorem ordU_mk0_eq_one {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    ordU v (Units.mk0 π hπ) = 1 := by
  simp [ordU, hϖ]

def unrChar (c : ℂˣ) : (Fv v)ˣ →* ℂˣ where
  toFun u := c ^ ordU v u
  map_one' := by rw [ordU_one, zpow_zero]
  map_mul' a b := by rw [ordU_mul, zpow_add]

theorem unrChar_apply (c : ℂˣ) (u : (Fv v)ˣ) : unrChar v c u = c ^ ordU v u := rfl

theorem unrChar_eq_one_of_valued_eq_one (c : ℂˣ) {u : (Fv v)ˣ} (hu : Valued.v (u : Fv v) = 1) :
    unrChar v c u = 1 := by
  rw [unrChar_apply, ordU_eq_zero_of_valued_eq_one v hu, zpow_zero]

theorem unrChar_mk0 (c : ℂˣ) {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    unrChar v c (Units.mk0 π hπ) = c := by
  rw [unrChar_apply, ordU_mk0_eq_one v hπ hϖ, zpow_one]

def w0 : G2 v :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_w0 : ((w0 v : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0] := rfl

section Twist

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem log_qC : Complex.log (Ideal.absNorm v.asIdeal : ℂ) = ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) := by
  rw [qC_eq, ← Complex.ofReal_log (qR_pos v).le]

theorem qC_cpow_cpow (y z : ℂ) (hy : y.im = 0) :
    ((Ideal.absNorm v.asIdeal : ℂ) ^ y) ^ z = (Ideal.absNorm v.asIdeal : ℂ) ^ (y * z) := by
  have hlog : (Complex.log (Ideal.absNorm v.asIdeal : ℂ)).im = 0 := by rw [log_qC]; exact Complex.ofReal_im _
  rw [Complex.cpow_mul]
  · rw [Complex.mul_im, hlog, hy]; simp [Real.pi_pos]
  · rw [Complex.mul_im, hlog, hy]; simp [Real.pi_pos.le]

theorem norm_eq_of_valued_eq_exp {m : ℤ} {a : Fv v} (ha : Valued.v a = WithZero.exp m) :
    ‖a‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, ha, WithZero.exp,
    WithZeroMulInt.toNNReal_neg_apply _ (WithZero.coe_ne_zero), WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow]
  rfl

theorem coe_modulus_eq_norm (x : Fv v) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

theorem norm_units_eq (u : (Fv v)ˣ) : ‖(u : Fv v)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordU v u) :=
  norm_eq_of_valued_eq_exp v (valued_eq_exp_neg_ordU v u)

private theorem _root_.SlMID.modulus_units_ne_zero (u : (Fv v)ˣ) : (((modulus (u : Fv v) : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
  rw [coe_modulus_eq_norm]
  exact_mod_cast (norm_pos_iff.mpr u.ne_zero).ne'

p2m_export "SlMID" "modulus_units_ne_zero"

theorem modulus_cpow (u : (Fv v)ˣ) (S : ℂ) :
    (((modulus (u : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ S = ((Ideal.absNorm v.asIdeal : ℂ) ^ (-S)) ^ (ordU v u) := by
  rw [coe_modulus_eq_norm, norm_units_eq, Complex.ofReal_zpow, ← qC_eq, ← Complex.cpow_intCast,
    qC_cpow_cpow v _ _ (by simp), ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

theorem unrChar_eq_modulus_cpow (c : ℂˣ) (t : ℂ) (hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-t) = c) (a : (Fv v)ˣ) :
    ((unrChar v c a : ℂˣ) : ℂ) = (((modulus (a : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ t := by
  rw [modulus_cpow, hc, unrChar_apply, Units.val_zpow_eq_zpow_val]

theorem exists_cpow_neg_eq (c : ℂˣ) : ∃ t : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-t) = c := by
  have hlog0 : ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (one_lt_qR v)).ne'
  refine ⟨-(Complex.log (c : ℂ) / ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ)), ?_⟩
  rw [neg_neg, Complex.cpow_def_of_ne_zero (qC_ne_zero v), log_qC, mul_div_cancel₀ _ hlog0, Complex.exp_log c.ne_zero]

variable {c : ℂˣ} {t : ℂ}

theorem twist_pt (hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-t) = c) (a : (Fv v)ˣ) (X s : ℂ) :
    X * ((unrChar v c a : ℂˣ) : ℂ) * (((modulus (a : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) =
      X * (((1 : (Fv v)ˣ →* ℂˣ) a : ℂˣ) : ℂ) * (((modulus (a : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (s + t - 1) := by
  rw [unrChar_eq_modulus_cpow v c t hc, MonoidHom.one_apply, Units.val_one, mul_one, mul_assoc,
    ← Complex.cpow_add _ _ (modulus_units_ne_zero v a)]
  congr 2
  ring

theorem twist_pt_inv (hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-t) = c) (a : (Fv v)ˣ) (X s : ℂ) :
    X * (((unrChar v c)⁻¹ a : ℂˣ) : ℂ) * (((modulus (a : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) =
      X * (((1 : (Fv v)ˣ →* ℂˣ)⁻¹ a : ℂˣ) : ℂ) * (((modulus (a : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (s - t - 1) := by
  simp only [inv_one, MonoidHom.inv_apply, MonoidHom.one_apply, Units.val_one, Units.val_inv_eq_inv_val, mul_one,
    unrChar_eq_modulus_cpow v c t hc]
  rw [mul_assoc, ← Complex.cpow_neg, ← Complex.cpow_add _ _ (modulus_units_ne_zero v a)]
  congr 2
  ring

theorem localZeta30_unrChar (hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-t) = c)
    (μ : Measure (Fv v)ˣ) (W : LocalGL3 v → ℂ) (s : ℂ) (g : LocalGL3 v) :
    localZeta30 v μ W (unrChar v c) s g = localZeta30 v μ W 1 (s + t) g := by
  unfold localZeta30
  congr 1
  funext a
  exact twist_pt v hc a _ s

theorem isLocalZeta30ConvergentAbove_unrChar (hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-t) = c)
    (μ : Measure (Fv v)ˣ) (W : LocalGL3 v → ℂ) (g : LocalGL3 v) {σ₀ : ℝ}
    (h : IsLocalZeta30ConvergentAbove v μ W 1 g σ₀) :
    IsLocalZeta30ConvergentAbove v μ W (unrChar v c) g (σ₀ - t.re) := by
  intro s hs
  have h' := h (s + t) (by rw [Complex.add_re]; linarith)
  refine h'.congr (Filter.Eventually.of_forall fun a => ?_)
  exact (twist_pt v hc a _ s).symm

theorem localZetaDual31_unrChar (hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-t) = c)
    (μ : Measure (Fv v)ˣ) (ν : Measure (Fv v)) (W : LocalGL3 v → ℂ) (s : ℂ) (g : LocalGL3 v) :
    localZetaDual31 v μ ν W (unrChar v c) (1 - s) g = localZetaDual31 v μ ν W 1 (1 - (s + t)) g := by
  unfold localZetaDual31 localZeta31
  congr 1
  funext a
  rw [show 1 - (s + t) = (1 - s) - t by ring]
  exact twist_pt_inv v hc a _ (1 - s)

theorem isLocalZeta31ConvergentAbove_unrChar_inv (hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-t) = c)
    (μ : Measure (Fv v)ˣ) (ν : Measure (Fv v)) (W : LocalGL3 v → ℂ) (g : LocalGL3 v) {σ₁ : ℝ}
    (h : IsLocalZeta31ConvergentAbove v μ ν W 1 g σ₁) :
    IsLocalZeta31ConvergentAbove v μ ν W (unrChar v c)⁻¹ g (σ₁ + t.re) := by
  intro s hs
  have h' := h (s - t) (by rw [Complex.sub_re]; linarith)
  refine h'.congr (Filter.Eventually.of_forall fun p => ?_)
  exact (twist_pt_inv v hc p.1 _ s).symm

end Twist
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section Shell31

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem measurable_ordU : Measurable (ordU v) := by
  refine measurable_to_countable' fun n => ?_
  have hset : ordU v ⁻¹' {n} = Units.val ⁻¹' Metric.sphere (0 : Fv v) ((Ideal.absNorm v.asIdeal : ℝ) ^ (-n)) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, mem_sphere_zero_iff_norm]
    constructor
    · intro h
      rw [norm_units_eq, h]
    · intro h
      rw [norm_units_eq] at h
      have hinj := zpow_right_injective₀ (qR_pos v) (one_lt_qR v).ne' h
      have : -ordU v u = -n := hinj
      linarith
  rw [hset]
  exact (Metric.isClosed_sphere.preimage Units.continuous_val).measurableSet

def ordShell (n : ℤ) : Set (Fv v)ˣ := {a | ordU v a = n}

theorem measurableSet_ordShell (n : ℤ) : MeasurableSet (ordShell v n) :=
  measurable_ordU v (measurableSet_singleton n)

theorem iUnion_ordShell : (⋃ n : ℤ, ordShell v n) = Set.univ := by
  ext a
  simp only [Set.mem_iUnion, ordShell, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨_, rfl⟩

theorem pairwise_disjoint_ordShell : Pairwise (fun m n : ℤ => Disjoint (ordShell v m) (ordShell v n)) := by
  intro m n hmn
  rw [Set.disjoint_left]
  intro a ha hb
  exact hmn (ha.symm.trans hb)

theorem unrChar_mul_modulus_cpow_of_mem_ordShell (c : ℂˣ) (s : ℂ) {a : (Fv v)ˣ} {n : ℤ} (ha : a ∈ ordShell v n) :
    ((unrChar v c a : ℂˣ) : ℂ) * (((modulus (a : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) =
      ((c : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ n := by
  have ha' : ordU v a = n := ha
  rw [unrChar_apply, Units.val_zpow_eq_zpow_val, modulus_cpow v a (s - 1), ha', mul_zpow]

theorem hasSum_shell_localZeta31 (c : ℂˣ) (τ : Measure (Fv v)ˣ) (ν : Measure (Fv v)) [SFinite ν]
    (V : LocalGL3 v → ℂ) (s : ℂ) (g : LocalGL3 v)
    (hint : Integrable (fun r : (Fv v)ˣ × Fv v =>
      V (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * g) * ((unrChar v c r.1 : ℂˣ) : ℂ) *
        (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (s - 1)) (τ.prod ν)) :
    HasSum (fun n : ℤ => ((c : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ n *
        ∫ a in ordShell v n, (∫ x, V (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) ∂τ)
      (localZeta31 v τ ν V (unrChar v c) s g) ∧
    Summable (fun n : ℤ => ‖((c : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ n *
        ∫ a in ordShell v n, (∫ x, V (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) ∂τ‖) := by

  set F : (Fv v)ˣ → ℂ := fun a =>
    (∫ x, V (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) * ((unrChar v c a : ℂˣ) : ℂ) *
      (((modulus (a : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) with hF
  have hFint : Integrable F τ := by
    have h := hint.integral_prod_left
    refine h.congr (ae_of_all _ fun a => ?_)
    show (∫ x, V (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) * ((unrChar v c a : ℂˣ) : ℂ) *
        (((modulus (a : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (s - 1) ∂ν) = F a
    rw [hF, integral_mul_const, integral_mul_const]

  have hshell : ∀ n : ℤ, ∫ a in ordShell v n, F a ∂τ =
      ((c : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ n *
        ∫ a in ordShell v n, (∫ x, V (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) ∂τ := by
    intro n
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_ordShell v n) fun a ha => ?_
    show F a = _
    rw [hF]
    beta_reduce
    rw [mul_assoc, unrChar_mul_modulus_cpow_of_mem_ordShell v c s ha, mul_comm]

  have hsum := hasSum_integral_iUnion (μ := τ) (f := F) (measurableSet_ordShell v)
    (pairwise_disjoint_ordShell v) (by rw [iUnion_ordShell]; exact hFint.integrableOn)
  rw [iUnion_ordShell, Measure.restrict_univ] at hsum
  have hZ : (∫ a, F a ∂τ) = localZeta31 v τ ν V (unrChar v c) s g := by rw [hF]; rfl
  refine ⟨?_, ?_⟩
  · rw [← hZ]
    exact hsum.congr_fun fun n => (hshell n).symm
  ·
    have hsumN := hasSum_integral_iUnion (μ := τ) (f := fun a => ‖F a‖) (measurableSet_ordShell v)
      (pairwise_disjoint_ordShell v) (by rw [iUnion_ordShell]; exact hFint.norm.integrableOn)
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsumN.summable
    rw [← hshell n]
    exact norm_integral_le_integral_norm _

end Shell31
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section ShellCalc

open scoped Pointwise

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem exists_eq_mk0_zpow_mul {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (t : (Fv v)ˣ) :
    ∃ ε : (Fv v)ˣ, Valued.v (ε : Fv v) = 1 ∧ t = Units.mk0 π hπ ^ ordU v t * ε := by
  refine ⟨(Units.mk0 π hπ ^ ordU v t)⁻¹ * t, ?_, by rw [mul_inv_cancel_left]⟩
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_mul, map_inv₀,
    map_zpow₀, hϖ, valued_eq_exp_neg_ordU, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add,
    smul_eq_mul]
  convert WithZero.exp_zero using 2
  ring

theorem ordShell_eq_smul (π : Fv v) (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    ordShell v n = (Units.mk0 π hπ ^ n) • ordShell v 0 := by
  ext t
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [ordShell, Set.mem_setOf_eq, smul_eq_mul, ordU_mul]
  have h1 : ordU v (Units.mk0 π hπ ^ n)⁻¹ = -n := by
    have := ordU_mul v (Units.mk0 π hπ ^ n)⁻¹ (Units.mk0 π hπ ^ n)
    rw [inv_mul_cancel, ordU_one] at this
    have h2 : ordU v (Units.mk0 π hπ ^ n) = n := by
      simp [ordU, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul]
    omega
  rw [h1]
  omega

theorem measure_ordShell (π : Fv v) (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    (τ : Measure (Fv v)ˣ) [τ.IsMulLeftInvariant] (n : ℤ) : τ (ordShell v n) = τ (ordShell v 0) := by
  rw [ordShell_eq_smul v π hπ hϖ n, measure_smul]

theorem ordShell_zero_eq : ordShell v 0 = {u : (Fv v)ˣ | Valued.v (u : Fv v) = 1} := by
  ext u
  show ordU v u = 0 ↔ Valued.v (u : Fv v) = 1
  have h := valued_eq_exp_neg_ordU v u
  constructor
  · intro h0; rw [h, h0, neg_zero, WithZero.exp_zero]
  · intro h1
    rw [h1, ← WithZero.exp_zero] at h
    have := congrArg WithZero.log h
    rw [WithZero.log_exp, WithZero.log_exp] at this
    omega

theorem hasSum_shell_of_forall_mem_ordShell (τ : Measure (Fv v)ˣ) (F : (Fv v)ˣ → ℂ) (hF : Integrable F τ)
    (φ : ℤ → ℂ) (hφ : ∀ n : ℤ, ∀ t ∈ ordShell v n, F t = φ n) :
    HasSum (fun n : ℤ => ((τ (ordShell v n)).toReal : ℂ) * φ n) (∫ t, F t ∂τ) ∧
      Summable (fun n : ℤ => ‖((τ (ordShell v n)).toReal : ℂ) * φ n‖) := by
  have hshell : ∀ n : ℤ, ∫ t in ordShell v n, F t ∂τ = ((τ (ordShell v n)).toReal : ℂ) * φ n := by
    intro n
    rw [setIntegral_congr_fun (measurableSet_ordShell v n) (hφ n), setIntegral_const, Complex.real_smul]
    rfl
  have hsum := hasSum_integral_iUnion (μ := τ) (f := F) (measurableSet_ordShell v)
    (pairwise_disjoint_ordShell v) (by rw [iUnion_ordShell]; exact hF.integrableOn)
  rw [iUnion_ordShell, Measure.restrict_univ] at hsum
  refine ⟨hsum.congr_fun fun n => (hshell n).symm, ?_⟩
  have hsumN := hasSum_integral_iUnion (μ := τ) (f := fun a => ‖F a‖) (measurableSet_ordShell v)
    (pairwise_disjoint_ordShell v) (by rw [iUnion_ordShell]; exact hF.norm.integrableOn)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsumN.summable
  rw [← hshell n]
  exact norm_integral_le_integral_norm _

end ShellCalc
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section BulkPoint

variable {v}

theorem scalarPi_eq_diagUnits2 (π : Fv v) (hπ : π ≠ 0) :
    (scalarPi π hπ : G2 v) = diagUnits2 (Units.mk0 π hπ) (Units.mk0 π hπ) := by
  apply Units.ext
  rw [coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem diagUnitGL2_eq_diagUnits2 (u : (Fv v)ˣ) : (diagUnitGL2 u : G2 v) = diagUnits2 u 1 := by
  apply Units.ext
  rw [coe_diagUnits2, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnits2_mul_diagUnits2 (x x' y y' : (Fv v)ˣ) :
    (diagUnits2 x y * diagUnits2 x' y' : G2 v) = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def diagScalarHom : (Fv v)ˣ →* G2 v where
  toFun u := diagUnits2 u u
  map_one' := by
    apply Units.ext; rw [coe_diagUnits2]; ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by rw [diagUnits2_mul_diagUnits2]

theorem scalarPi_zpow_eq_diagUnits2 (π : Fv v) (hπ : π ≠ 0) (n : ℤ) :
    (scalarPi π hπ : G2 v) ^ n = diagUnits2 (Units.mk0 π hπ ^ n) (Units.mk0 π hπ ^ n) := by
  rw [scalarPi_eq_diagUnits2]
  exact (map_zpow (diagScalarHom (v := v)) (Units.mk0 π hπ) n).symm

theorem diagUnits2_lattice (π : Fv v) (hπ : π ≠ 0) (m n : ℤ) :
    (diagUnits2 (Units.mk0 π hπ ^ m * Units.mk0 π hπ ^ n) (Units.mk0 π hπ ^ n) : G2 v) =
      scalarPi π hπ ^ n * diagUnitGL2 (Units.mk0 π hπ ^ m) := by
  rw [scalarPi_zpow_eq_diagUnits2, diagUnitGL2_eq_diagUnits2, diagUnits2_mul_diagUnits2, mul_one, mul_comm]

theorem scalar_mul_comm (z : (Fv v)ˣ) (g : LocalGL3 v) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) z * g = g * Matrix.GeneralLinearGroup.scalar (Fin 3) z := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  exact (Matrix.scalar_commute (z : Fv v) (fun r => (Commute.all _ r)) _).eq

theorem diagUnits2_units_mem_K2 {ε₁ ε₂ : (Fv v)ˣ} (h₁ : Valued.v (ε₁ : Fv v) = 1) (h₂ : Valued.v (ε₂ : Fv v) = 1) :
    (diagUnits2 ε₁ ε₂ : G2 v) ∈ K2 v := by
  have hi₁ : Valued.v ((ε₁⁻¹ : (Fv v)ˣ) : Fv v) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, h₁, inv_one]
  have hi₂ : Valued.v ((ε₂⁻¹ : (Fv v)ˣ) : Fv v) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, h₂, inv_one]
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [coe_diagUnits2]; fin_cases i <;> fin_cases j <;> simp [h₁, h₂]
  · rw [show ((diagUnits2 ε₁ ε₂ : G2 v)⁻¹ : G2 v) = diagUnits2 ε₁⁻¹ ε₂⁻¹ from by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [diagUnits2_mul_diagUnits2, mul_inv_cancel, mul_inv_cancel]
        apply Units.ext; rw [coe_diagUnits2]; ext i j; fin_cases i <;> fin_cases j <;> simp, coe_diagUnits2]
    fin_cases i <;> fin_cases j <;> simp [h₁, h₂, hi₁, hi₂]

end BulkPoint
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section FibreAlgebra

def lcoeff (Q : Polynomial ℂ) (k : ℤ) : ℤ → ℂ := fun n => if 0 ≤ n + k then Q.coeff (n + k).toNat else 0

theorem lcoeff_eq_zero_of_lt (Q : Polynomial ℂ) (k : ℤ) {n : ℤ} (hn : n < -k) : lcoeff Q k n = 0 := by
  simp only [lcoeff]; rw [if_neg (by omega)]

theorem hasSum_lcoeff (Q : Polynomial ℂ) (k : ℤ) (X : ℂ) (hX : X ≠ 0) :
    HasSum (fun n : ℤ => lcoeff Q k n * X ^ n) (Q.eval X * X ^ (-k)) := by
  have hN : HasSum (fun m : ℕ => lcoeff Q k (-k + m) * X ^ m) (Q.eval X) := by
    have : (fun m : ℕ => lcoeff Q k (-k + m) * X ^ m) = fun m => Q.coeff m * X ^ m := by
      funext m; simp only [lcoeff]; rw [if_pos (by omega)]; congr 2; omega
    rw [this, Polynomial.eval_eq_sum]
    exact hasSum_sum_of_ne_finset_zero (fun m hm => by
      rw [Polynomial.mem_support_iff, not_not] at hm; rw [hm, zero_mul])
  have h := Ws1.Middle.Eval.hasSum_int_of_support (lcoeff Q k) (-k) (fun n hn => lcoeff_eq_zero_of_lt Q k hn) X hX
    _ hN
  rwa [mul_comm] at h

theorem tsum_lcoeff (Q : Polynomial ℂ) (k : ℤ) (X : ℂ) (hX : X ≠ 0) :
    ∑' n : ℤ, lcoeff Q k n * X ^ n = Q.eval X * X ^ (-k) := (hasSum_lcoeff Q k X hX).tsum_eq

theorem summable_norm_lcoeff (Q : Polynomial ℂ) (k : ℤ) (r : ℝ) : Summable fun n : ℤ => ‖lcoeff Q k n‖ * r ^ n := by
  refine summable_of_ne_finset_zero (s := (Q.support.image (fun m : ℕ => (m : ℤ) - k))) fun n hn => ?_
  simp only [lcoeff]
  split_ifs with h
  · have : Q.coeff (n + k).toNat = 0 := by
      by_contra hc
      exact hn (Finset.mem_image.mpr ⟨(n + k).toNat, Polynomial.mem_support_iff.mpr hc, by omega⟩)
    rw [this, norm_zero, zero_mul]
  · rw [norm_zero, zero_mul]

def lconv (b : ℤ → ℂ) (p : Polynomial ℂ) : ℤ → ℂ := fun n => ∑ j ∈ p.support, p.coeff j * b (n - j)

theorem lconv_eq_lcoeff_of_forall (b : ℤ → ℂ) (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) {ρ : ℝ} (hρ : 0 < ρ)
    (H : ∀ X : ℂ, X ≠ 0 → ‖X‖ < ρ →
      Summable (fun n : ℤ => ‖b n * X ^ n‖) ∧ (∑' n : ℤ, b n * X ^ n) * Q₂.eval X = Q₁.eval X * X ^ (-k)) :
    lconv b Q₂ = lcoeff Q₁ k := by

  have key : ∀ X : ℂ, X ≠ 0 → ‖X‖ < ρ →
      Summable (fun n : ℤ => ‖(lconv b Q₂ n - lcoeff Q₁ k n) * X ^ n‖) ∧
        ∑' n : ℤ, (lconv b Q₂ n - lcoeff Q₁ k n) * X ^ n = 0 := by
    intro X hX hXρ
    obtain ⟨hs, hid⟩ := H X hX hXρ
    have hconv := Ws1.Middle.Laurent.tsum_mul_eval_eq_tsum_conv b X hX hs Q₂
    have hsconv := Ws1.Middle.Laurent.summable_norm_conv_mul_zpow b X hX hs Q₂
    have hconv' : (∑' n : ℤ, b n * X ^ n) * Q₂.eval X = ∑' n : ℤ, lconv b Q₂ n * X ^ n := hconv
    have hsconv' : Summable (fun n : ℤ => ‖lconv b Q₂ n * X ^ n‖) := hsconv
    have hsL : Summable (fun n : ℤ => ‖lcoeff Q₁ k n * X ^ n‖) := by
      simpa only [norm_mul, norm_zpow] using summable_norm_lcoeff Q₁ k ‖X‖
    refine ⟨?_, ?_⟩
    · refine (hsconv'.add hsL).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      rw [sub_mul]; exact norm_sub_le _ _
    · rw [show (fun n : ℤ => (lconv b Q₂ n - lcoeff Q₁ k n) * X ^ n) =
          fun n => lconv b Q₂ n * X ^ n - lcoeff Q₁ k n * X ^ n from funext fun n => sub_mul _ _ _,
        (hsconv'.of_norm.hasSum.sub (hasSum_lcoeff Q₁ k X hX)).tsum_eq, ← hconv', hid, sub_self]

  have h1 := key ((ρ / 3 : ℝ) : ℂ) (by exact_mod_cast (by positivity : (ρ / 3 : ℝ) ≠ 0)) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith)
  have h2 := key ((2 * ρ / 3 : ℝ) : ℂ) (by exact_mod_cast (by positivity : (2 * ρ / 3 : ℝ) ≠ 0)) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith)
  have e := Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
    (fun n => lconv b Q₂ n - lcoeff Q₁ k n) (r₁ := ρ / 3) (r₂ := 2 * ρ / 3) (by positivity) (by linarith)
    (by simpa only [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < ρ / 3)]
      using h1.1)
    (by simpa only [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < 2 * ρ / 3)] using h2.1)
    (fun z hz1 hz2 => (key z (by rintro rfl; simp at hz1; linarith) (by linarith)).2)
  funext n
  exact sub_eq_zero.mp (congrFun e n)

theorem tsum_mul_eval_eq_of_forall (b : ℤ → ℂ) (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) {ρ : ℝ} (hρ : 0 < ρ)
    (H : ∀ X : ℂ, X ≠ 0 → ‖X‖ < ρ →
      Summable (fun n : ℤ => ‖b n * X ^ n‖) ∧ (∑' n : ℤ, b n * X ^ n) * Q₂.eval X = Q₁.eval X * X ^ (-k))
    (X : ℂ) (hX : X ≠ 0) (hb : Summable fun n : ℤ => ‖b n * X ^ n‖) :
    (∑' n : ℤ, b n * X ^ n) * Q₂.eval X = Q₁.eval X * X ^ (-k) := by
  have hconv := Ws1.Middle.Laurent.tsum_mul_eval_eq_tsum_conv b X hX hb Q₂
  rw [hconv, show (fun n : ℤ => (∑ j ∈ Q₂.support, Q₂.coeff j * b (n - j)) * X ^ n) =
    fun n => lconv b Q₂ n * X ^ n from rfl, lconv_eq_lcoeff_of_forall b Q₁ Q₂ k hρ H, tsum_lcoeff Q₁ k X hX]

theorem tsum_mul_eval_eq_of_mul_eval_eq_zero (b : ℤ → ℂ) (PL PN Q : Polynomial ℂ) (κ : ℤ) (hQ : Q ≠ 0)
    {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hs₁ : Summable fun n : ℤ => ‖b n‖ * r₁ ^ n) (hs₂ : Summable fun n : ℤ => ‖b n‖ * r₂ ^ n)
    (hz : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ →
      ((∑' n : ℤ, b n * z ^ n) * PL.eval z - PN.eval z * z ^ (-κ)) * Q.eval z = 0)
    (X : ℂ) (hX1 : r₁ ≤ ‖X‖) (hX2 : ‖X‖ ≤ r₂) :
    (∑' n : ℤ, b n * X ^ n) * PL.eval X = PN.eval X * X ^ (-κ) := by

  have hsum : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → Summable fun n : ℤ => ‖b n * z ^ n‖ := by
    intro z hz1 hz2
    simpa only [norm_mul, norm_zpow] using Ws1.Middle.Laurent.summable_norm_mul_pow_of_le_of_le b h0 hz1 hz2 hs₁ hs₂
  have hne : ∀ z : ℂ, r₁ ≤ ‖z‖ → z ≠ 0 := fun z hz h0' => by rw [h0', norm_zero] at hz; linarith

  set e : ℤ → ℂ := fun n => lconv b PL n - lcoeff PN κ n with he
  have key : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ →
      Summable (fun n : ℤ => ‖e n * z ^ n‖) ∧
        ∑' n : ℤ, e n * z ^ n = (∑' n : ℤ, b n * z ^ n) * PL.eval z - PN.eval z * z ^ (-κ) := by
    intro z hz1 hz2
    have hconv := Ws1.Middle.Laurent.tsum_mul_eval_eq_tsum_conv b z (hne z hz1) (hsum z hz1 hz2) PL
    have hsconv := Ws1.Middle.Laurent.summable_norm_conv_mul_zpow b z (hne z hz1) (hsum z hz1 hz2) PL
    have hconv' : (∑' n : ℤ, b n * z ^ n) * PL.eval z = ∑' n : ℤ, lconv b PL n * z ^ n := hconv
    have hsconv' : Summable (fun n : ℤ => ‖lconv b PL n * z ^ n‖) := hsconv
    have hsL : Summable (fun n : ℤ => ‖lcoeff PN κ n * z ^ n‖) := by
      simpa only [norm_mul, norm_zpow] using summable_norm_lcoeff PN κ ‖z‖
    refine ⟨?_, ?_⟩
    · refine (hsconv'.add hsL).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      rw [he, sub_mul]; exact norm_sub_le _ _
    · rw [show (fun n : ℤ => e n * z ^ n) = fun n => lconv b PL n * z ^ n - lcoeff PN κ n * z ^ n from
          funext fun n => by rw [he, sub_mul],
        (hsconv'.of_norm.hasSum.sub (hasSum_lcoeff PN κ z (hne z hz1))).tsum_eq, ← hconv']

  have he0 : e = 0 := by
    refine Ws1.Middle.Laurent.eq_zero_of_tsum_mul_eval_eq_zero e h0 h12 ?_ ?_ Q hQ fun z hz1 hz2 => ?_
    · simpa only [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
        using (key (r₁ : ℂ) (by simp [abs_of_pos h0]) (by simp [abs_of_pos h0]; exact h12.le)).1
    · simpa only [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h0.trans h12)]
        using (key (r₂ : ℂ) (by simp [abs_of_pos (h0.trans h12)]; exact h12.le) (by simp [abs_of_pos (h0.trans h12)])).1
    · rw [(key z hz1.le hz2.le).2]; exact hz z hz1.le hz2.le
  have := (key X hX1 hX2).2
  rw [he0] at this
  simp only [Pi.zero_apply, zero_mul, tsum_zero] at this
  exact (sub_eq_zero.mp this.symm)

end FibreAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section Fibre2a

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

variable {v}

theorem qC_cpow_neg_sub_one (s : ℂ) :
    (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1)) = (Ideal.absNorm v.asIdeal : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
  rw [show -(s - 1) = 1 + -s by ring, Complex.cpow_add _ _ (qC_ne_zero v), Complex.cpow_one]

theorem qC_cpow_intCast_mul (k : ℤ) (s : ℂ) :
    (Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℂ) * s) = ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (-k) := by
  rw [show (k : ℂ) * s = ((-k : ℤ) : ℂ) * (-s) by push_cast; ring, Complex.cpow_int_mul]

theorem exists_cpow_neg_eq_of_ne_zero {Y : ℂ} (hY : Y ≠ 0) :
    ∃ S : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-S) = Y ∧ (Ideal.absNorm v.asIdeal : ℝ) ^ (-S.re) = ‖Y‖ := by
  obtain ⟨S, hS⟩ := exists_cpow_neg_eq v (Units.mk0 Y hY)
  refine ⟨S, hS, ?_⟩
  rw [← Complex.neg_re, ← norm_qC_cpow, hS, Units.val_mk0]

def shellCoeff (c : ℂˣ) (τ : Measure (Fv v)ˣ) (ν : Measure (Fv v)) (V : LocalGL3 v → ℂ) (g : LocalGL3 v) (n : ℤ) : ℂ :=
  (∫ a in ordShell v n, (∫ x, V (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) ∂τ) *
    ((c : ℂ) * (Ideal.absNorm v.asIdeal : ℂ)) ^ n

theorem shell_series_localZeta31 (c : ℂˣ) (τ : Measure (Fv v)ˣ) (ν : Measure (Fv v)) [SFinite ν]
    (V : LocalGL3 v → ℂ) (g : LocalGL3 v) (s : ℂ)
    (hint : Integrable (fun r : (Fv v)ˣ × Fv v =>
      V (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * g) * ((unrChar v c r.1 : ℂˣ) : ℂ) *
        (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (s - 1)) (τ.prod ν)) :
    Summable (fun n : ℤ => ‖shellCoeff c τ ν V g n * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n‖) ∧
      ∑' n : ℤ, shellCoeff c τ ν V g n * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n =
        localZeta31 v τ ν V (unrChar v c) s g := by
  obtain ⟨hsum, hsm⟩ := hasSum_shell_localZeta31 v c τ ν V s g hint
  have hterm : ∀ n : ℤ, ((c : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1))) ^ n *
      (∫ a in ordShell v n, (∫ x, V (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) ∂τ) =
      shellCoeff c τ ν V g n * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n := by
    intro n
    rw [shellCoeff, qC_cpow_neg_sub_one, ← mul_assoc, mul_zpow]; ring
  simp_rw [hterm] at hsum hsm
  exact ⟨hsm, hsum.tsum_eq⟩

theorem localZeta31_mul_eval_eq (c : ℂˣ) (τ : Measure (Fv v)ˣ) (ν : Measure (Fv v)) [SFinite ν]
    (V : LocalGL3 v → ℂ) (g : LocalGL3 v) (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) (σ₀ : ℝ)
    (hc31 : IsLocalZeta31ConvergentAbove v τ ν V (unrChar v c) g σ₀)
    (hZ1 : ∀ s : ℂ, σ₀ < s.re → localZeta31 v τ ν V (unrChar v c) s g * Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
      Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℂ) * s))
    (X : ℂ) (hX : X ≠ 0) (hb : Summable fun n : ℤ => ‖shellCoeff c τ ν V g n * X ^ n‖) :
    (∑' n : ℤ, shellCoeff c τ ν V g n * X ^ n) * Q₂.eval X = Q₁.eval X * X ^ (-k) := by
  refine tsum_mul_eval_eq_of_forall (shellCoeff c τ ν V g) Q₁ Q₂ k (ρ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ₀))
    (Real.rpow_pos_of_pos (qR_pos v) _) (fun Y hY hYlt => ?_) X hX hb
  obtain ⟨s', hs', hs'n⟩ := exists_cpow_neg_eq_of_ne_zero (v := v) hY
  have hre : σ₀ < s'.re := by
    rw [← hs'n, Real.rpow_lt_rpow_left_iff (one_lt_qR v)] at hYlt; linarith
  obtain ⟨hsm, hsum⟩ := shell_series_localZeta31 c τ ν V g s' (hc31 s' hre)
  rw [hs'] at hsm hsum
  refine ⟨hsm, ?_⟩
  rw [hsum, ← hs', hZ1 s' hre, qC_cpow_intCast_mul]

end Fibre2a
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section LaurentPoly

def IsLaurentPolyFn (f : ℂ → ℂ) : Prop := ∃ (P : Polynomial ℂ) (J : ℤ), ∀ z : ℂ, z ≠ 0 → f z = P.eval z * z ^ (-J)

theorem IsLaurentPolyFn.congr {f g : ℂ → ℂ} (hf : IsLaurentPolyFn f) (h : ∀ z : ℂ, z ≠ 0 → g z = f z) :
    IsLaurentPolyFn g := by
  obtain ⟨P, J, hP⟩ := hf; exact ⟨P, J, fun z hz => (h z hz).trans (hP z hz)⟩

theorem IsLaurentPolyFn.const (c : ℂ) : IsLaurentPolyFn fun _ => c :=
  ⟨Polynomial.C c, 0, fun z hz => by simp⟩

theorem IsLaurentPolyFn.eval (p : Polynomial ℂ) : IsLaurentPolyFn fun z => p.eval z :=
  ⟨p, 0, fun z hz => by simp⟩

theorem IsLaurentPolyFn.mul {f g : ℂ → ℂ} (hf : IsLaurentPolyFn f) (hg : IsLaurentPolyFn g) :
    IsLaurentPolyFn fun z => f z * g z := by
  obtain ⟨P, J, hP⟩ := hf
  obtain ⟨P', J', hP'⟩ := hg
  refine ⟨P * P', J + J', fun z hz => ?_⟩
  show f z * g z = _
  rw [hP z hz, hP' z hz, Polynomial.eval_mul, neg_add, zpow_add₀ hz]; ring

theorem IsLaurentPolyFn.add {f g : ℂ → ℂ} (hf : IsLaurentPolyFn f) (hg : IsLaurentPolyFn g) :
    IsLaurentPolyFn fun z => f z + g z := by
  obtain ⟨P, J, hP⟩ := hf
  obtain ⟨P', J', hP'⟩ := hg
  refine ⟨P * Polynomial.X ^ (max J J' - J).toNat + P' * Polynomial.X ^ (max J J' - J').toNat, max J J',
    fun z hz => ?_⟩
  show f z + g z = _
  have k1 : z ^ ((max J J' - J).toNat : ℕ) * z ^ (-max J J') = z ^ (-J) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ hz]; congr 1; ring
  have k2 : z ^ ((max J J' - J').toNat : ℕ) * z ^ (-max J J') = z ^ (-J') := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ hz]; congr 1; ring
  rw [hP z hz, hP' z hz, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_pow, Polynomial.eval_X, add_mul, mul_assoc, k1, mul_assoc, k2]

theorem IsLaurentPolyFn.sub {f g : ℂ → ℂ} (hf : IsLaurentPolyFn f) (hg : IsLaurentPolyFn g) :
    IsLaurentPolyFn fun z => f z - g z :=
  (hf.add ((IsLaurentPolyFn.const (-1)).mul hg)).congr fun z hz => by ring

theorem IsLaurentPolyFn.zpow (j : ℤ) : IsLaurentPolyFn fun z => z ^ j := by
  rcases le_or_gt 0 j with hj | hj
  · refine ⟨Polynomial.X ^ j.toNat, 0, fun z hz => ?_⟩
    rw [Polynomial.eval_pow, Polynomial.eval_X, neg_zero, zpow_zero, mul_one, ← zpow_natCast,
      Int.toNat_of_nonneg hj]
  · refine ⟨1, -j, fun z hz => ?_⟩
    rw [Polynomial.eval_one, one_mul, neg_neg]

theorem IsLaurentPolyFn.eval_mul_inv (p : Polynomial ℂ) (κ : ℂ) : IsLaurentPolyFn fun z => p.eval (κ * z⁻¹) := by
  classical
  refine ⟨∑ j ∈ p.support, Polynomial.C (p.coeff j * κ ^ j) * Polynomial.X ^ (p.natDegree - j), p.natDegree,
    fun z hz => ?_⟩
  show p.eval (κ * z⁻¹) = _
  conv_lhs => rw [Polynomial.eval_eq_sum]
  rw [Polynomial.eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : j ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
  show p.coeff j * (κ * z⁻¹) ^ j = _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have key : (z ^ (p.natDegree - j) : ℂ) * z ^ (-(p.natDegree : ℤ)) = (z ^ j)⁻¹ := by
    rw [← zpow_natCast, Nat.cast_sub hjd, ← zpow_add₀ hz, ← zpow_natCast, ← zpow_neg]; congr 1; ring
  rw [mul_pow, inv_pow, show p.coeff j * κ ^ j * z ^ (p.natDegree - j) * z ^ (-(p.natDegree : ℤ)) =
    p.coeff j * κ ^ j * (z ^ (p.natDegree - j) * z ^ (-(p.natDegree : ℤ))) by ring, key]
  ring

theorem IsLaurentPolyFn.eq_zero {f : ℂ → ℂ} (hf : IsLaurentPolyFn f) {R₁ R₂ : ℝ} (h0 : 0 ≤ R₁) (h12 : R₁ < R₂)
    (hz : ∀ z : ℂ, R₁ < ‖z‖ → ‖z‖ < R₂ → f z = 0) (z : ℂ) (hz0 : z ≠ 0) : f z = 0 := by
  obtain ⟨P, J, hP⟩ := hf
  have hroots : Set.Infinite {x : ℂ | P.IsRoot x} := by
    have hsub : ((fun r : ℝ => (r : ℂ)) '' Set.Ioo R₁ R₂) ⊆ {x : ℂ | P.IsRoot x} := by
      rintro _ ⟨r, ⟨hr1, hr2⟩, rfl⟩
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (h0.trans_lt hr1).ne'
      have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h0.trans_lt hr1)]
      have := hz r (by rw [hnr]; exact hr1) (by rw [hnr]; exact hr2)
      rw [hP r hr0, mul_eq_zero] at this
      rcases this with h | h
      · exact h
      · exact absurd h (zpow_ne_zero _ hr0)
    exact ((Set.Ioo_infinite h12).image Complex.ofReal_injective.injOn).mono hsub
  rw [hP z hz0, Polynomial.eq_zero_of_infinite_isRoot P hroots, Polynomial.eval_zero, zero_mul]

theorem IsLaurentPolyFn.eq_of_eqOn {f g : ℂ → ℂ} (hf : IsLaurentPolyFn f) (hg : IsLaurentPolyFn g) {R₁ R₂ : ℝ}
    (h0 : 0 ≤ R₁) (h12 : R₁ < R₂) (hz : ∀ z : ℂ, R₁ < ‖z‖ → ‖z‖ < R₂ → f z = g z) (z : ℂ) (hz0 : z ≠ 0) :
    f z = g z :=
  sub_eq_zero.mp (IsLaurentPolyFn.eq_zero (hf.sub hg) h0 h12 (fun z h1 h2 => sub_eq_zero.mpr (hz z h1 h2)) z hz0)

theorem tsum_mul_laurent_eq_of_mul_eval_eq_zero (b : ℤ → ℂ) {L Nf : ℂ → ℂ} (hL : IsLaurentPolyFn L)
    (hN : IsLaurentPolyFn Nf) (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hs₁ : Summable fun n : ℤ => ‖b n‖ * r₁ ^ n) (hs₂ : Summable fun n : ℤ => ‖b n‖ * r₂ ^ n)
    (hz : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → ((∑' n : ℤ, b n * z ^ n) * L z - Nf z) * Q.eval z = 0)
    (X : ℂ) (hX1 : r₁ ≤ ‖X‖) (hX2 : ‖X‖ ≤ r₂) :
    (∑' n : ℤ, b n * X ^ n) * L X = Nf X := by
  obtain ⟨PL, JL, hPL⟩ := hL
  obtain ⟨PN, JN, hPN⟩ := hN
  have hne : ∀ z : ℂ, r₁ ≤ ‖z‖ → z ≠ 0 := fun z hz h0' => by rw [h0', norm_zero] at hz; linarith
  have key := tsum_mul_eval_eq_of_mul_eval_eq_zero b PL PN Q (JN - JL) hQ h0 h12 hs₁ hs₂ (fun z hz1 hz2 => by
    have hz0 := hne z hz1
    have h := hz z hz1 hz2
    rw [hPL z hz0, hPN z hz0] at h
    have e1 : z ^ JL * z ^ (-JL) = 1 := by rw [← zpow_add₀ hz0, add_neg_cancel, zpow_zero]
    have e2 : z ^ (-(JN - JL)) = z ^ JL * z ^ (-JN) := by rw [show -(JN - JL) = JL + -JN by ring, zpow_add₀ hz0]
    calc ((∑' n : ℤ, b n * z ^ n) * PL.eval z - PN.eval z * z ^ (-(JN - JL))) * Q.eval z
        = z ^ JL * ((((∑' n : ℤ, b n * z ^ n) * (PL.eval z * z ^ (-JL))) - PN.eval z * z ^ (-JN)) * Q.eval z) := by
          rw [e2]
          have : (∑' n : ℤ, b n * z ^ n) * PL.eval z = (∑' n : ℤ, b n * z ^ n) * PL.eval z * (z ^ JL * z ^ (-JL)) := by
            rw [e1, mul_one]
          rw [this]; ring
      _ = 0 := by rw [h, mul_zero]) X hX1 hX2
  have hX0 := hne X hX1
  rw [hPL X hX0, hPN X hX0]
  calc (∑' n : ℤ, b n * X ^ n) * (PL.eval X * X ^ (-JL)) = ((∑' n : ℤ, b n * X ^ n) * PL.eval X) * X ^ (-JL) := by ring
    _ = PN.eval X * X ^ (-(JN - JL)) * X ^ (-JL) := by rw [key]
    _ = PN.eval X * X ^ (-JN) := by rw [mul_assoc, ← zpow_add₀ hX0]; congr 2; ring

end LaurentPoly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

section CellPrep

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem setOf_valued_le_one_eq : {y : Fv v | Valued.v y ≤ 1} = Metric.closedBall (0 : Fv v) 1 := by
  ext y
  simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  by_cases hy : y = 0
  · subst hy; simp
  · have hv : Valued.v y = WithZero.exp (-ordU v (Units.mk0 y hy)) := valued_eq_exp_neg_ordU v (Units.mk0 y hy)
    rw [norm_eq_of_valued_eq_exp v hv, hv, ← WithZero.exp_zero, WithZero.exp_le_exp]
    constructor
    · intro h; exact zpow_le_one_of_nonpos₀ (one_lt_qR v).le (by omega)
    · intro h
      by_contra hc
      push Not at hc
      have : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordU v (Units.mk0 y hy)) :=
        one_lt_zpow₀ (one_lt_qR v) (by omega)
      linarith

theorem measurableSet_valued_le_one : MeasurableSet {y : Fv v | Valued.v y ≤ 1} := by
  rw [setOf_valued_le_one_eq]; exact Metric.isClosed_closedBall.measurableSet

end CellPrep
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2"

end SlMID
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

noncomputable section

namespace SlMID

open scoped NNReal ENNReal

theorem laurent_identity_persist (b : ℤ → ℂ) {L Nf : ℂ → ℂ} (hL : IsLaurentPolyFn L) (hN : IsLaurentPolyFn Nf)
    {ρ : ℝ} (hρ : 0 < ρ)
    (H : ∀ X : ℂ, X ≠ 0 → ‖X‖ < ρ → Summable (fun n : ℤ => ‖b n * X ^ n‖) ∧ (∑' n : ℤ, b n * X ^ n) * L X = Nf X)
    (X : ℂ) (hX : X ≠ 0) (hb : Summable fun n : ℤ => ‖b n * X ^ n‖) :
    (∑' n : ℤ, b n * X ^ n) * L X = Nf X := by
  obtain ⟨PL, JL, hPL⟩ := hL
  obtain ⟨PN, JN, hPN⟩ := hN

  have H' : ∀ Y : ℂ, Y ≠ 0 → ‖Y‖ < ρ →
      Summable (fun n : ℤ => ‖b n * Y ^ n‖) ∧ (∑' n : ℤ, b n * Y ^ n) * PL.eval Y = PN.eval Y * Y ^ (-(JN - JL)) := by
    intro Y hY hYρ
    obtain ⟨hs, hid⟩ := H Y hY hYρ
    refine ⟨hs, ?_⟩
    rw [hPL Y hY, hPN Y hY] at hid
    have e1 : Y ^ JL * Y ^ (-JL) = 1 := by rw [← zpow_add₀ hY, add_neg_cancel, zpow_zero]
    have e2 : Y ^ (-(JN - JL)) = Y ^ (-JN) * Y ^ JL := by rw [show -(JN - JL) = -JN + JL by ring, zpow_add₀ hY]
    calc (∑' n : ℤ, b n * Y ^ n) * PL.eval Y = (∑' n : ℤ, b n * Y ^ n) * (PL.eval Y * Y ^ (-JL)) * Y ^ JL := by
          rw [mul_assoc, mul_assoc, mul_comm (Y ^ (-JL)), e1, mul_one]
      _ = PN.eval Y * Y ^ (-JN) * Y ^ JL := by rw [hid]
      _ = PN.eval Y * Y ^ (-(JN - JL)) := by rw [e2, mul_assoc]
  have key := tsum_mul_eval_eq_of_forall b PN PL (JN - JL) hρ H' X hX hb
  rw [hPL X hX, hPN X hX]
  have e2 : X ^ (-(JN - JL)) = X ^ (-JN) * X ^ JL := by rw [show -(JN - JL) = -JN + JL by ring, zpow_add₀ hX]
  have e1 : X ^ JL * X ^ (-JL) = 1 := by rw [← zpow_add₀ hX, add_neg_cancel, zpow_zero]
  calc (∑' n : ℤ, b n * X ^ n) * (PL.eval X * X ^ (-JL)) = ((∑' n : ℤ, b n * X ^ n) * PL.eval X) * X ^ (-JL) := by ring
    _ = PN.eval X * X ^ (-(JN - JL)) * X ^ (-JL) := by rw [key]
    _ = PN.eval X * X ^ (-JN) := by rw [e2, mul_assoc, mul_assoc, e1, mul_one]

theorem eq_unrChar_of_unramified (v : HeightOneSpectrum (𝓞 ℚ)) {π : Fv v} (hπ : π ≠ 0)
    (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (χ : (Fv v)ˣ →* ℂˣ)
    (hχu : ∀ e : (Fv v)ˣ, Valued.v (e : Fv v) = 1 → χ e = 1) :
    χ = unrChar v (χ (Units.mk0 π hπ)) := by
  ext a
  obtain ⟨ε, hε, ha⟩ := exists_eq_mk0_zpow_mul v hπ hϖ a
  rw [unrChar_apply]
  conv_lhs => rw [ha]
  rw [map_mul, hχu ε hε, mul_one, map_zpow]

theorem IsLaurentPolyFn.eval_mul (p : Polynomial ℂ) (κ : ℂ) : IsLaurentPolyFn fun z => p.eval (κ * z) :=
  ⟨p.comp (Polynomial.C κ * Polynomial.X), 0, fun z hz => by simp [Polynomial.eval_comp]⟩

section DualW1

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem dual_T2core_at {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    (Vd : LocalGL3 v → ℂ) (χ : (Fv v)ˣ →* ℂˣ) (hχu : ∀ e : (Fv v)ˣ, Valued.v (e : Fv v) = 1 → χ e = 1)
    (g : LocalGL3 v) (α₁ A1 ε ωn μ₁ : ℂ) (hα₁ : α₁ ≠ 0) (hA1 : A1 ≠ 0) (E Ed D₀₁ R : Polynomial ℂ) (ℓ : ℕ) (N₀ : ℤ)
    (σn : ℝ)
    (hconv : IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (selfDualHaarAt ℚ v) Vd χ g σn)
    (hid : ∀ s : ℂ, σn < (1 - s).re →
      localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Vd χ (1 - s) g *
          Ed.eval (A1⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * D₀₁.eval (α₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) =
        ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * (α₁ ^ ℓ)⁻¹ * E.eval (A1 * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * ωn⁻¹ *
          (μ₁ * ((α₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ N₀ * R.eval (α₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)))))
    (s : ℂ)
    (hint : Integrable (fun r : (Fv v)ˣ × Fv v =>
      Vd (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * g) * ((χ r.1 : ℂˣ) : ℂ) *
        (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ ((1 - s) - 1))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) :
    localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Vd χ (1 - s) g *
        Ed.eval (A1⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * D₀₁.eval (α₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) =
      ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * (α₁ ^ ℓ)⁻¹ * E.eval (A1 * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * ωn⁻¹ *
        (μ₁ * ((α₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ N₀ * R.eval (α₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)))) := by
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := qC_ne_zero v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt v

  have hχ := eq_unrChar_of_unramified v hπ hϖ χ hχu
  set c : ℂˣ := χ (Units.mk0 π hπ) with hc

  have conv : ∀ w : ℂ,
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - (1 - w))) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w) ∧
      (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - (1 - w)) = ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w))⁻¹ ∧
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - (1 - w))) = ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w))⁻¹) ^ ℓ ∧
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 - w) + 1 / 2)) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 / 2 : ℂ)) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w))⁻¹ := by
    intro w
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show -(1 / 2 - (1 - w)) = (1 : ℂ) / 2 + -w by ring, Complex.cpow_add _ _ hq0]
    · rw [show (1 : ℂ) - (1 - w) = -(-w) by ring, Complex.cpow_neg]
    · rw [show (ℓ : ℂ) * (1 / 2 - (1 - w)) = ℓ * (-(1 / 2 : ℂ) + -(-w)) by ring, Complex.cpow_nat_mul,
        Complex.cpow_add _ _ hq0, Complex.cpow_neg _ (-w)]
    · rw [show -((1 - w) + 1 / 2) = -(3 / 2 : ℂ) + -(-w) by ring, Complex.cpow_add _ _ hq0, Complex.cpow_neg _ (-w)]
  set L : ℂ → ℂ := fun X => Ed.eval (A1⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * X)) * D₀₁.eval (α₁⁻¹ * X⁻¹) with hL
  set Nf : ℂ → ℂ := fun X => ε * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * X⁻¹) ^ ℓ * (α₁ ^ ℓ)⁻¹ *
      E.eval (A1 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 / 2 : ℂ)) * X⁻¹)) * ωn⁻¹ * (μ₁ * ((α₁⁻¹ * X⁻¹) ^ N₀ * R.eval (α₁⁻¹ * X⁻¹))) with hNf
  have hLL : IsLaurentPolyFn L := by
    refine ((IsLaurentPolyFn.eval_mul Ed (A1⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2))).mul
      (IsLaurentPolyFn.eval_mul_inv D₀₁ α₁⁻¹)).congr fun z hz => ?_
    rw [hL]; beta_reduce; rw [mul_assoc]
  have hNN : IsLaurentPolyFn Nf := by
    have h1 : IsLaurentPolyFn fun X : ℂ => ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * X⁻¹) ^ ℓ :=
      ((IsLaurentPolyFn.const (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) ^ ℓ)).mul (IsLaurentPolyFn.zpow (-(ℓ : ℤ)))).congr
        fun z hz => by rw [mul_pow, ← zpow_natCast z⁻¹, inv_zpow']
    have h2 : IsLaurentPolyFn fun X : ℂ => E.eval (A1 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 / 2 : ℂ)) * X⁻¹)) :=
      (IsLaurentPolyFn.eval_mul_inv E (A1 * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(3 / 2 : ℂ)))).congr fun z hz => by rw [mul_assoc]
    have h3 : IsLaurentPolyFn fun X : ℂ => (α₁⁻¹ * X⁻¹) ^ N₀ :=
      ((IsLaurentPolyFn.const (α₁⁻¹ ^ N₀)).mul (IsLaurentPolyFn.zpow (-N₀))).congr fun z hz => by
        rw [mul_zpow, inv_zpow' z]
    have h4 : IsLaurentPolyFn fun X : ℂ => R.eval (α₁⁻¹ * X⁻¹) := IsLaurentPolyFn.eval_mul_inv R α₁⁻¹
    exact ((((((IsLaurentPolyFn.const ε).mul h1).mul (IsLaurentPolyFn.const (α₁ ^ ℓ)⁻¹)).mul h2).mul
      (IsLaurentPolyFn.const ωn⁻¹)).mul ((IsLaurentPolyFn.const μ₁).mul (h3.mul h4))).congr fun z hz => by
        rw [hNf]

  have key : ∀ w : ℂ, Integrable (fun r : (Fv v)ˣ × Fv v =>
      Vd (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * g) * ((unrChar v c r.1 : ℂˣ) : ℂ) *
        (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (w - 1))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) →
      Summable (fun n : ℤ => ‖shellCoeff c (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        Vd g n * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ n‖) ∧
      ∑' n : ℤ, shellCoeff c (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Vd g n *
        ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ n =
        localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Vd χ w g := by
    intro w hw
    have := shell_series_localZeta31 c _ _ Vd g w hw
    rw [← hχ] at this
    exact this
  have hidX : ∀ w : ℂ, σn < w.re →
      localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Vd χ w g *
        L ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) = Nf ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) := by
    intro w hw
    have h := hid (1 - w) (by rwa [sub_sub_cancel])
    obtain ⟨c1, c2, c3, c4⟩ := conv w
    rw [c2, c1, c3, c4, sub_sub_cancel] at h
    rw [hL, hNf]; beta_reduce
    rw [← h]; ring

  have hX0 : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hq0
  have hint' : Integrable (fun r : (Fv v)ˣ × Fv v =>
      Vd (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * g) * ((unrChar v c r.1 : ℂˣ) : ℂ) *
        (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ ((1 - s) - 1))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := by
    rw [← hχ]; exact hint
  obtain ⟨hb, hsum⟩ := key (1 - s) hint'
  have main := laurent_identity_persist _ hLL hNN (ρ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-σn))
    (Real.rpow_pos_of_pos (qR_pos v) _) (fun Y hY hYlt => ?_) _ hX0 hb
  · rw [hsum] at main
    obtain ⟨c1, c2, c3, c4⟩ := conv (1 - s)
    simp only [sub_sub_cancel] at c1 c2 c3 c4
    rw [c1, c2, c3, c4]
    rw [hL, hNf] at main
    have := main
    beta_reduce at this
    rw [← this]; ring
  · obtain ⟨w, hw, hwn⟩ := exists_cpow_neg_eq_of_ne_zero (v := v) hY
    have hre : σn < w.re := by
      rw [← hwn, Real.rpow_lt_rpow_left_iff (one_lt_qR v)] at hYlt; linarith
    have hI := hconv w hre
    rw [hχ] at hI
    obtain ⟨hb', hsum'⟩ := key w hI
    rw [hw] at hb' hsum'
    refine ⟨hb', ?_⟩
    rw [hsum', ← hw]
    exact hidX w hre

theorem dual_T2core₀_at {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    (Vd : LocalGL3 v → ℂ) (χ : (Fv v)ˣ →* ℂˣ) (hχu : ∀ e : (Fv v)ˣ, Valued.v (e : Fv v) = 1 → χ e = 1)
    (g : LocalGL3 v) (σn : ℝ)
    (hconv : IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (selfDualHaarAt ℚ v) Vd χ g σn)
    (hid : ∀ s : ℂ, σn < (1 - s).re →
      localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Vd χ (1 - s) g = 0)
    (s : ℂ)
    (hint : Integrable (fun r : (Fv v)ˣ × Fv v =>
      Vd (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * g) * ((χ r.1 : ℂˣ) : ℂ) *
        (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ ((1 - s) - 1))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v))) :
    localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Vd χ (1 - s) g = 0 := by
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := qC_ne_zero v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt v
  have hχ := eq_unrChar_of_unramified v hπ hϖ χ hχu
  set c : ℂˣ := χ (Units.mk0 π hπ) with hc
  have key : ∀ w : ℂ, Integrable (fun r : (Fv v)ˣ × Fv v =>
      Vd (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * g) * ((unrChar v c r.1 : ℂˣ) : ℂ) *
        (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (w - 1))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) →
      Summable (fun n : ℤ => ‖shellCoeff c (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        Vd g n * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ n‖) ∧
      ∑' n : ℤ, shellCoeff c (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Vd g n *
        ((Ideal.absNorm v.asIdeal : ℂ) ^ (-w)) ^ n =
        localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) Vd χ w g := by
    intro w hw
    have := shell_series_localZeta31 c _ _ Vd g w hw
    rw [← hχ] at this
    exact this
  have hX0 : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hq0
  have hint' : Integrable (fun r : (Fv v)ˣ × Fv v =>
      Vd (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * g) * ((unrChar v c r.1 : ℂˣ) : ℂ) *
        (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ ((1 - s) - 1))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := by
    rw [← hχ]; exact hint
  obtain ⟨hb, hsum⟩ := key (1 - s) hint'
  have main := laurent_identity_persist _ (IsLaurentPolyFn.const 1) (IsLaurentPolyFn.const 0)
    (ρ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-σn)) (Real.rpow_pos_of_pos (qR_pos v) _) (fun Y hY hYlt => ?_) _ hX0 hb
  · rw [hsum, mul_one] at main; exact main
  · obtain ⟨w, hw, hwn⟩ := exists_cpow_neg_eq_of_ne_zero (v := v) hY
    have hre : σn < w.re := by
      rw [← hwn, Real.rpow_lt_rpow_left_iff (one_lt_qR v)] at hYlt; linarith
    have hI := hconv w hre
    rw [hχ] at hI
    obtain ⟨hb', hsum'⟩ := key w hI
    rw [hw] at hb' hsum'
    refine ⟨hb', ?_⟩
    rw [hsum', mul_one]
    have h := hid (1 - w) (by rwa [sub_sub_cancel])
    rwa [sub_sub_cancel] at h

end DualW1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

section HintBridge

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem measure_ordShell_zero_ne_zero {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    (τ : Measure (Fv v)ˣ) [τ.IsMulLeftInvariant] [NeZero τ] : τ (ordShell v 0) ≠ 0 := by
  intro h0
  have hall : ∀ n : ℤ, τ (ordShell v n) = 0 := fun n => by rw [measure_ordShell v π hπ hϖ τ n, h0]
  have : τ Set.univ = 0 := by rw [← iUnion_ordShell v]; exact measure_iUnion_null hall
  exact (NeZero.ne τ) (Measure.measure_univ_eq_zero.mp this)

theorem integrable_fibre_lattice_of_integrable4 {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    (Vf : LocalGL3 v → ℂ) (hK : ∀ k ∈ K2 v, ∀ g : LocalGL3 v, Vf (g * iotaGL k) = Vf g)
    (χ : Fin 2 → ((Fv v)ˣ →* ℂˣ)) (f : G2 v → ℂ) (w₀ : G2 v)
    (hfne : ∀ y : Fv v, Valued.v y ≤ 1 → f (w₀ * unipotentGL2 y) ≠ 0) (w : ℂ)
    (h4 : Integrable (fun q : Fv v × (Fv v)ˣ × (Fv v)ˣ × Fv v =>
      f (w₀ * unipotentGL2 q.1) *
        (((χ 0 q.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.1 : Fv v) : ℝ) : ℂ) ^ (w - 1)) *
        (Vf (iotaGL (diagUnitGL2 q.2.2.1) * lowerUnipotent21 q.2.2.2 * iotaGL (diagUnits2 1 q.2.1 * unipotentGL2 q.1)) *
          ((χ 1 q.2.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.2.1 : Fv v) : ℝ) : ℂ) ^ (w - 1)))
      ((selfDualHaarAt ℚ v).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)))))
    (n : ℤ) :
    Integrable (fun r : (Fv v)ˣ × Fv v =>
      Vf (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * iotaGL (diagUnits2 1 (Units.mk0 π hπ ^ n))) *
        ((χ 1 r.1 : ℂˣ) : ℂ) * (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (w - 1))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := by
  set τ : Measure (Fv v)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) with hτ
  set ν : Measure (Fv v) := selfDualHaarAt ℚ v with hν
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt v
  haveI hτH : τ.IsHaarMeasure := by rw [hτ]; exact isHaarMeasure_mulHaar v
  set e := (MeasurableEquiv.prodAssoc : (Fv v × (Fv v)ˣ) × ((Fv v)ˣ × Fv v) ≃ᵐ Fv v × (Fv v)ˣ × (Fv v)ˣ × Fv v)
    with he
  set F4 := (fun q : Fv v × (Fv v)ˣ × (Fv v)ˣ × Fv v =>
      f (w₀ * unipotentGL2 q.1) *
        (((χ 0 q.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.1 : Fv v) : ℝ) : ℂ) ^ (w - 1)) *
        (Vf (iotaGL (diagUnitGL2 q.2.2.1) * lowerUnipotent21 q.2.2.2 * iotaGL (diagUnits2 1 q.2.1 * unipotentGL2 q.1)) *
          ((χ 1 q.2.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.2.1 : Fv v) : ℝ) : ℂ) ^ (w - 1))) with hF4
  have h4' : Integrable (F4 ∘ e) ((ν.prod τ).prod (τ.prod ν)) := by
    refine (integrable_map_equiv e F4).mp ?_
    rw [he, Measure.prodAssoc_prod]; exact h4
  set fib : Fv v × (Fv v)ˣ → (Fv v)ˣ × Fv v → ℂ := fun p r =>
    Vf (iotaGL (diagUnitGL2 r.1) * lowerUnipotent21 r.2 * iotaGL (diagUnits2 1 p.2 * unipotentGL2 p.1)) *
      ((χ 1 r.1 : ℂˣ) : ℂ) * (((modulus (r.1 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (w - 1) with hfib
  set Cst : Fv v × (Fv v)ˣ → ℂ := fun p =>
    f (w₀ * unipotentGL2 p.1) * (((χ 0 p.2 : ℂˣ) : ℂ) * (((modulus (p.2 : Fv v) : ℝ≥0) : ℝ) : ℂ) ^ (w - 1)) with hCst
  have hF4e : ∀ p r, (F4 ∘ e) (p, r) = Cst p * fib p r := by
    intro p r
    simp only [Function.comp_apply, he, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, hF4,
      hCst, hfib]
    all_goals ring
  have hGae : ∀ᵐ p ∂(ν.prod τ), p ∈ {y : Fv v | Valued.v y ≤ 1} ×ˢ ordShell v n → Integrable (fib p) (τ.prod ν) := by
    filter_upwards [h4'.prod_right_ae] with p hp hmem
    have hC : Cst p ≠ 0 := by
      rw [hCst]
      exact mul_ne_zero (hfne p.1 (Set.mem_prod.mp hmem).1) (mul_ne_zero (Units.ne_zero _) (by
        rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; left; exact modulus_units_ne_zero v p.2))
    refine (hp.const_mul (Cst p)⁻¹).congr (ae_of_all _ fun r => ?_)
    show (Cst p)⁻¹ * (F4 ∘ e) (p, r) = fib p r
    rw [hF4e, inv_mul_cancel_left₀ hC]
  have hcell : (ν.prod τ) ({y : Fv v | Valued.v y ≤ 1} ×ˢ ordShell v n) ≠ 0 := by
    rw [Measure.prod_prod]
    refine mul_ne_zero ?_ ?_
    · rw [setOf_valued_le_one_eq v]; exact (Metric.measure_closedBall_pos ν _ one_pos).ne'
    · rw [measure_ordShell v π hπ hϖ τ n]; exact measure_ordShell_zero_ne_zero v hπ hϖ τ
  have hmeas : MeasurableSet ({y : Fv v | Valued.v y ≤ 1} ×ˢ ordShell v n) :=
    (measurableSet_valued_le_one v).prod (measurableSet_ordShell v n)
  haveI : NeZero ((ν.prod τ).restrict ({y : Fv v | Valued.v y ≤ 1} ×ˢ ordShell v n)) :=
    ⟨by rwa [Ne, Measure.restrict_eq_zero]⟩
  obtain ⟨p, hpmem, hpint⟩ : ∃ p : Fv v × (Fv v)ˣ, p ∈ {y : Fv v | Valued.v y ≤ 1} ×ˢ ordShell v n ∧
      (p ∈ {y : Fv v | Valued.v y ≤ 1} ×ˢ ordShell v n → Integrable (fib p) (τ.prod ν)) :=
    ((ae_restrict_mem hmeas).and (ae_restrict_of_ae hGae)).exists
  have hI := hpint hpmem
  obtain ⟨hy, ha⟩ := Set.mem_prod.mp hpmem
  obtain ⟨ε, hε, hpa⟩ := exists_eq_mk0_zpow_mul v hπ hϖ p.2
  have han : ordU v p.2 = n := ha
  rw [han] at hpa
  have hk : (diagUnits2 1 ε * unipotentGL2 p.1 : G2 v) ∈ K2 v :=
    Subgroup.mul_mem _ (diagUnits2_units_mem_K2 (by simp) hε) (unipotentGL2_mem_K2 v hy)
  have hsplit : (diagUnits2 1 p.2 * unipotentGL2 p.1 : G2 v) =
      diagUnits2 1 (Units.mk0 π hπ ^ n) * (diagUnits2 1 ε * unipotentGL2 p.1) := by
    rw [← mul_assoc, diagUnits2_mul_diagUnits2, one_mul, ← hpa]
  refine hI.congr (ae_of_all _ fun r => ?_)
  rw [hfib]
  beta_reduce
  rw [hsplit, MonoidHom.map_mul iotaGL, ← mul_assoc, hK _ hk]

end HintBridge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

end SlMID
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace Ws1
namespace Middle
namespace DualGlue

theorem hasSum_bulkShells (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ v
    HasSum (fun j : ℕ => ((((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v (-(j : ℤ)))).toReal : ℝ) : ℂ))
      ((((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal : ℝ) : ℂ) := by
  letI := localBorel ℚ v
  haveI := Ws1.Middle.DualKit.isAddHaarMeasure_selfDualHaarAt v
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one hq1
  have hqm1 : (Ideal.absNorm v.asIdeal : ℝ) - 1 ≠ 0 := (sub_pos.mpr hq1).ne'
  have hne : (1 : ℝ) - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ≠ 0 := (sub_pos.mpr (inv_lt_one_of_one_lt₀ hq1)).ne'
  have hF : ∀ j : ℕ, ((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v (-(j : ℤ)))).toReal =
      (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) * ((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal *
        ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ j := by
    intro j
    have h := Ws1.Middle.ShellMass.measureReal_sphere v (-(j : ℤ)) (selfDualHaarAt ℚ v)
    rw [show Ws1.Middle.Cells.yShell v (-(j : ℤ)) = {y : v.adicCompletion ℚ | Valued.v y = WithZero.exp (-(j : ℤ))}
      from rfl, h]
    rw [show (-(j : ℤ) - 1) = -((j : ℤ) + 1) by ring, zpow_neg, zpow_neg, zpow_natCast, zpow_add₀ hq0.ne',
      zpow_natCast, zpow_one, inv_pow]
    field_simp
  have hgeo : HasSum (fun j : ℕ => ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ j) (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹ :=
    hasSum_geometric_of_lt_one (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq1)
  have hR : HasSum (fun j : ℕ => ((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v (-(j : ℤ)))).toReal)
      (((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal) := by
    have h := hgeo.mul_left ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
      ((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal)
    rw [show (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) * ((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal *
        (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹ = ((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal by
      field_simp] at h
    exact h.congr_fun fun j => hF j
  exact hR.map Complex.ofRealHom.toAddMonoidHom Complex.continuous_ofReal

theorem shellMass_pos (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℤ) :
    letI := localBorel ℚ v
    ((((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v (k))).toReal : ℝ) : ℂ) =
      (((((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹)) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ k := by
  letI := localBorel ℚ v
  haveI := Ws1.Middle.DualKit.isAddHaarMeasure_selfDualHaarAt v
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have h := Ws1.Middle.ShellMass.measureReal_sphere v k (selfDualHaarAt ℚ v)
  rw [show Ws1.Middle.Cells.yShell v k = {y : v.adicCompletion ℚ | Valued.v y = WithZero.exp k} from rfl, h]
  push_cast
  rw [zpow_sub_one₀ hq0]
  ring

set_option maxHeartbeats 12000000 in

theorem S1_of_cells
    (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0) (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (V : LocalGL3 v → ℂ) (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (w₀ : GL (Fin 2) (v.adicCompletion ℚ))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (E Ed : Polynomial ℂ) (ε : ℂ)
    (a₁ a₂ u : ℂ) (ha : a₁ * a₂ ≠ 0) (cK : ℝ) (α₀ : ℂ)
    (hαa : α₀ * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2))
    (hfD1 : fD 1 = ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹)
    (N₀ : ℤ) (D₀₁ D₀₂ : Polynomial ℂ) (P₀ : MvPolynomial (Fin 2) ℂ)
    (Nt : ℤ) (Dt₁ Dt₂ : Polynomial ℂ) (Pt : MvPolynomial (Fin 2) ℂ)
    (row₀ : ℕ → Polynomial ℂ) (s : ℂ)
    (hT1 : letI := localBorel ℚ v
      Summable (fun p : ℤ × ℤ => ‖Ws1.Middle.Cells.dualCell hπ V ℓ χD fD w₀ p.1 p.2 s‖) ∧
      (∫ y, (∫ a, Ws1.Middle.Cells.dualCellIntegrand hπ V ℓ χD fD w₀ s y a ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) =
        ∑' p : ℤ × ℤ, Ws1.Middle.Cells.dualCell hπ V ℓ χD fD w₀ p.1 p.2 s)
    (hbulk : letI := localBorel ℚ v
      ∀ k : ℤ, k ≤ 0 → ∀ n : ℤ, Ws1.Middle.Cells.dualCell hπ V ℓ χD fD w₀ k n s = ((((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v (k))).toReal : ℝ) : ℂ) * ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (fD 1 * (α₀ ^ (n) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) * localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n))))))))
    (htail : letI := localBorel ℚ v
      ∀ k : ℤ, 1 ≤ k → ∀ n : ℤ, Ws1.Middle.Cells.dualCell hπ V ℓ χD fD w₀ k n s =
        ((((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v (k))).toReal : ℝ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-2 * k) * ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (fD 1 * (α₀ ^ (n + k) * (Ideal.absNorm v.asIdeal : ℂ) ^ (((n + k : ℤ) : ℂ) * s) * localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n + k))))))))
    (hcore : letI := localBorel ℚ v
      ∀ n : ℤ, N₀ ≤ n →
        localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n)))) * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * D₀₁.eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) =
          ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ * E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * ((((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n)⁻¹ *
            ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * ((dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) ^ N₀ * (row₀ (n - N₀).toNat).eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s))))
    (hcore₀ : letI := localBorel ℚ v
      ∀ n : ℤ, n < N₀ → localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n)))) = 0)
    (hresum : Summable (fun j : ℕ => ‖(row₀ j).eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) * (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) ^ j‖) ∧
      (∑' j : ℕ, (row₀ j).eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) * (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) ^ j) * D₀₂.eval (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) = MvPolynomial.eval ![dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s, dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s] P₀)
    (hNumDen : torusNum Nt Pt (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen D₀₁ D₀₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) =
      torusNum N₀ P₀ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen Dt₁ Dt₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s)) :
    letI := localBorel ℚ v
    ((cK : ℂ) * ∫ y, fD (w₀ * unipotentGL2 y) *
            (∫ a, ((χD 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1) *
              localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 a * unipotentGL2 y))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) *
          Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
          (torusDen D₀₁ D₀₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen Dt₁ Dt₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * dualWtD v s) =
        dualCNum v E Ed ε ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (dualC0 v ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ)) s *
          (torusNum N₀ P₀ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen Dt₁ Dt₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * dualWtD v s +
            dualWtN v s * torusNum Nt Pt (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen D₀₁ D₀₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s)) := by
  letI := localBorel ℚ v
  haveI := Ws1.Middle.DualKit.isAddHaarMeasure_selfDualHaarAt v

  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hNcpow : ∀ w : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ w ≠ 0 := fun w h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hq1 : ‖((Ideal.absNorm v.asIdeal : ℂ))⁻¹‖ < 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have ha₂ : a₂ ≠ 0 := right_ne_zero_of_mul ha
  have hA2 : (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) ≠ 0 := mul_ne_zero ha₂ (hNcpow _)
  have hω0 : ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hα₀' : α₀ = dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) := by
    unfold dualAlpha0
    rw [← hαa, mul_assoc, mul_inv_cancel₀ hA2, mul_one]
  have hα₀0 : α₀ ≠ 0 := by rw [hα₀']; unfold dualAlpha0; exact mul_ne_zero (hNcpow _) (inv_ne_zero hA2)
  have hY0 : dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s ≠ 0 := by
    unfold dualY dualAlpha0
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hNcpow _) (inv_ne_zero hA2)) (inv_ne_zero hω0)) (hNcpow _)
  have hμ₀ : (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) = 1 := by
    rw [Ws1.Middle.SelfDualMass.selfDualHaarAt_real_integers_eq_one v]; simp
  have hμ₀' : (((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal : ℂ) = 1 := by
    rw [← hμ₀]; rfl

  have hYpow : ∀ n : ℤ, α₀ ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) * ((((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n)⁻¹ = (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) ^ n := by
    intro n
    rw [← hα₀']
    unfold dualY
    rw [mul_zpow, mul_zpow, ← Complex.cpow_int_mul, inv_zpow]
    ring

  have hG := lattice_sum_identity
    (fun k n => Ws1.Middle.Cells.dualCell hπ V ℓ χD fD w₀ k n s)
    (fun n => (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (fD 1 * (α₀ ^ (n) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) * localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n)))))))
    (fun k => ((((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v (k))).toReal : ℝ) : ℂ))
    (Ideal.absNorm v.asIdeal : ℂ) (((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal : ℂ)
    ((((selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x ≤ 1}).toReal : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹))
    ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * fD 1 * ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ * E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) ^ N₀)
    (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) (Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) (D₀₁.eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s)) (D₀₂.eval (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s))
    hN0 hq1 hY0 N₀ row₀ P₀ hT1.1 hbulk htail
    (by show ((((selfDualHaarAt ℚ v) (Ws1.Middle.Cells.yShell v 0)).toReal : ℝ) : ℂ) ≠ 0
        rw [shellMass_pos v 0, zpow_zero, mul_one, hμ₀', one_mul, sub_ne_zero, ne_comm]
        intro h
        have h1 : (Ideal.absNorm v.asIdeal : ℂ) = 1 := inv_eq_one.mp h
        have : (Ideal.absNorm v.asIdeal : ℕ) = 1 := by exact_mod_cast h1
        have := NumberField.HeightOneSpectrum.one_lt_absNorm v
        omega)
    (hasSum_bulkShells v)
    (fun k hk => shellMass_pos v k)
    rfl
    (by
      intro n hn
      have h := hcore n hn
      calc (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (fD 1 * (α₀ ^ (n) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) * localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n)))))) * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * D₀₁.eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s)
          = (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * fD 1 * (α₀ ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) *
              (localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n)))) * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * D₀₁.eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s)) := by ring
        _ = (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * fD 1 * (α₀ ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) *
              (ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ * E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * ((((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n)⁻¹ *
                ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * ((dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) ^ N₀ * (row₀ (n - N₀).toNat).eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s)))) := by rw [h]
        _ = ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * fD 1 * ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ * E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) ^ N₀) *
              (α₀ ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) * ((((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n)⁻¹) * (row₀ (n - N₀).toNat).eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) := by ring
        _ = _ := by rw [hYpow n])
    (by
      intro n hn
      show (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * (fD 1 * (α₀ ^ (n) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s) * localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n)))))) = 0
      rw [hcore₀ n hn]; simp)
    hresum

  have hU : (∫ y, fD (w₀ * unipotentGL2 y) *
            (∫ a, ((χD 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1) *
              localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 a * unipotentGL2 y))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) = ∑' p : ℤ × ℤ, Ws1.Middle.Cells.dualCell hπ V ℓ χD fD w₀ p.1 p.2 s := by
    rw [← hT1.2]
    congr 1
    funext y
    unfold Ws1.Middle.Cells.dualCellIntegrand
    exact (integral_const_mul _ _).symm

  have hconst : (cK : ℂ) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * (1 + ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * dualWtD v s * ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * fD 1 * ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ * E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) ^ N₀) =
      dualCNum v E Ed ε ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (dualC0 v ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ)) s * (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) ^ N₀ *
        (dualWtD v s + dualWtN v s) := by
    simp only [dualCNum, dualC0, dualWtD, dualWtN]
    rw [hfD1, hμ₀]
    ring
  rw [hμ₀'] at hG
  rw [hU]
  have hND := hNumDen
  simp only [torusNum, torusDen] at hND ⊢
  linear_combination ((cK : ℂ) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * (Polynomial.eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) Dt₁ * Polynomial.eval (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) Dt₂) * dualWtD v s) * hG +
    (-(dualCNum v E Ed ε ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (dualC0 v ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ)) s * dualWtN v s)) * hND +
    ((Polynomial.eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) Dt₁ * Polynomial.eval (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) Dt₂) * (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) ^ N₀ * MvPolynomial.eval ![dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s, dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s] P₀) * hconst

end Ws1.Middle.DualGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

noncomputable section

namespace Ws1
namespace Middle

set_option maxHeartbeats 16000000 in
theorem dual_transport
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (hE : E ≠ 0) (hEd : Ed ≠ 0)
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) :
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∀ (cK : ℝ) (_hcK : 0 < cK),
      ∀ u : ℂ, ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) < ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re →
      ∀ (α₀ α₁ : ℂ) (_hα : α₀ ≠ 0 ∧ α₁ ≠ 0) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
        (_hχDu : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
        (_hα₀ : ((χD 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₀) (_hα₁ : ((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₁)

        (_hαa : α₀ * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) ∧ α₁ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2))
        (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (_hfD : fD ∈ principalSeries2 v χD)
        (_hfDK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → fD (g * k) = fD g)
        (_hfD1 : fD 1 = ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹)
        (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (_hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
        (σc : ℝ) (_hσc : ∀ s : ℂ, σc < (1 - s).re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            ((fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (iotaGL g) * fD (w₀ * g)) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
                ((1 - s) - 1 / 2)) μ₂),
      ∃ (m₁d m₂d : Polynomial ℂ) (kd : ℤ) (σt : ℝ), m₂d ≠ 0 ∧
        IsDualMiddleDatum v hπ V E Ed ε ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ)
          ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) m₁d m₂d kd ∧
        ∀ s : ℂ, σt < (1 - s).re →
          ((cK : ℂ) * ∫ y, fD (w₀ * unipotentGL2 y) *
            (∫ a, ((χD 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1) *
              localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 a * unipotentGL2 y))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) *
              Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
              Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
              m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s) := by
  intro μ₂ _ μN _ cK hcK u hu α₀ α₁ hα χD hχDu hα₀ hα₁ hαa fD hfD hfDK hfD1 w₀ hw₀ σc hσc
  letI := localBorel ℚ v
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  have hVsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, V (g * k) = V g := Ws1.Middle.DualKit.smooth_of_mem_gl3CyclicSubspace hsm hVmem
  have hψ : ψv ≠ 1 := by
    rw [hψinv]; exact inv_ne_one.mpr (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v)

  have hΦ₀mem : (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) ∈ gl3CyclicSubspace W :=
    gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hVmem
  have hΦ₀sm := Ws1.Middle.DualKit.smooth_rightTranslate hVsm (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ)))
  obtain ⟨N₀, D₀₁, D₀₂, P₀, r₀, hTV₀⟩ :=
    LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
      v ψv hψ W hW hsm hadm ωv hω hπ hϖ (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) hΦ₀mem hΦ₀sm
  have hTD₀ : IsTorusDatum v hπ (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) N₀ D₀₁ D₀₂ P₀ r₀ := hTV₀
  have hΦtmem : (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) ∈ gl3CyclicSubspace W :=
    gl3AmbientRightTranslate_mem_gl3CyclicSubspace W _ hVmem
  have hΦtsm := Ws1.Middle.DualKit.smooth_rightTranslate hVsm (longWeyl3 * weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ)))
  obtain ⟨Nt, Dt₁, Dt₂, Pt, rt, hTVt⟩ :=
    LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
      v ψv hψ W hW hsm hadm ωv hω hπ hϖ (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) hΦtmem hΦtsm
  have hTDt : IsTorusDatum v hπ (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) Nt Dt₁ Dt₂ Pt rt := hTVt
  obtain ⟨hD₀₁, hD₀₂, hr₀, hsupp₀, hser₀⟩ := hTV₀
  obtain ⟨hDt₁, hDt₂, hrt, hsuppt, hsert⟩ := hTVt
  obtain ⟨row₀, r₀₂, hr₀₂, hrow₀, hresum₀⟩ :=
    MvPolynomial.exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq _ D₀₁ D₀₂ P₀ r₀ hD₀₂ hr₀ hser₀
  obtain ⟨rowt, rt₂, hrt₂, hrowt, hresumt⟩ :=
    MvPolynomial.exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq _ Dt₁ Dt₂ Pt rt hDt₂ hrt hsert

  have S1 : ∃ (σt : ℝ), ∀ s : ℂ, σt < (1 - s).re →
      ((cK : ℂ) * ∫ y, fD (w₀ * unipotentGL2 y) *
            (∫ a, ((χD 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1) *
              localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 a * unipotentGL2 y))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) *
          Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
          (torusDen D₀₁ D₀₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen Dt₁ Dt₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * dualWtD v s) =
        dualCNum v E Ed ε ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (dualC0 v ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ)) s *
          (torusNum N₀ P₀ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen Dt₁ Dt₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * dualWtD v s +
            dualWtN v s * torusNum Nt Pt (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen D₀₁ D₀₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s)) := by
    have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    have hNcpow : ∀ w : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ w ≠ 0 := fun w h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have hq1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    have ha₁ : a₁ ≠ 0 := left_ne_zero_of_mul ha
    have ha₂ : a₂ ≠ 0 := right_ne_zero_of_mul ha
    have hA1 : (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) ≠ 0 := mul_ne_zero ha₁ (hNcpow _)
    have hA2 : (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) ≠ 0 := mul_ne_zero ha₂ (hNcpow _)
    have hω0 : ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _

    have hα₁' : ((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) := by
      rw [hα₁]; unfold dualAlpha1; rw [← hαa.2, mul_assoc, mul_inv_cancel₀ hA1, mul_one]

    have hμ₀1 : (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) = 1 := by
      rw [Ws1.Middle.SelfDualMass.selfDualHaarAt_real_integers_eq_one v]; simp
    have hJ : (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ ≠ 0 := by
      intro h
      have h1 : (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) = (Ideal.absNorm v.asIdeal : ℂ) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) := by
        have h' : ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ = 1 := by linear_combination -h
        have hNu : (Ideal.absNorm v.asIdeal : ℂ) ^ u ≠ 0 := hNcpow u
        have hNu' : (Ideal.absNorm v.asIdeal : ℂ) ^ (-u) ≠ 0 := hNcpow (-u)
        calc (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) = (((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((Ideal.absNorm v.asIdeal : ℂ) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) := by field_simp
          _ = (Ideal.absNorm v.asIdeal : ℂ) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) := by rw [h', one_mul]
      have hn1 : ‖(a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))‖ = ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) := by
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos (lt_trans zero_lt_one hq1), Complex.neg_re]
      have hn2 : ‖(a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)‖ = ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re := by
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos (lt_trans zero_lt_one hq1)]
      have h2 : ‖(a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))‖ = (Ideal.absNorm v.asIdeal : ℝ) * ‖(a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)‖ := by
        rw [h1, norm_mul, Complex.norm_natCast]
      have hN1 : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hq1.le
      have hpos : 0 < ‖(a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)‖ := norm_pos_iff.mpr hA2
      rw [← hn1, ← hn2] at hu
      nlinarith
    have hfD1ne : fD 1 ≠ 0 := by
      rw [hfD1, hμ₀1, one_mul]; exact inv_ne_zero hJ
    have hfne : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ 1 → fD (w₀ * unipotentGL2 y) ≠ 0 := by
      intro y hy
      rw [show fD (w₀ * unipotentGL2 y) = fD 1 by
        rw [← hfDK (w₀ * unipotentGL2 y) 1 (Subgroup.mul_mem _ (SlMID.w0_mem_K2 v hw₀) (SlMID.unipotentGL2_mem_K2 v hy)), one_mul]]
      exact hfD1ne

    have hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (g * iotaGL k) = (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) g :=
      fun k hk g => Ws1.Middle.Cells.dualTwist_iotaGL_invariant hπ V hVdK ℓ k hk g

    obtain ⟨σY, hσY⟩ := Ws1.Middle.DualGlue.exists_forall_norm_dualY_lt v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) hr₀₂
    refine ⟨max σc σY, fun s hs => ?_⟩
    have hsc : σc < (1 - s).re := lt_of_le_of_lt (le_max_left _ _) hs
    have hsY : σY < (1 - s).re := lt_of_le_of_lt (le_max_right _ _) hs
    have hI := hσc s hsc

    have hT1 := Ws46.MidT1.dual_unfold_eq_tsum_cells_of_integrable hπ hϖ V ℓ χD fD hfD w₀ hw₀ s μ₂ hI

    have hbulk : ∀ k : ℤ, k ≤ 0 → ∀ n : ℤ, _ := fun k hk n =>
      Ws1.Middle.Cells.dualCell_bulk_eq hπ hϖ V hVdK ℓ χD hχDu α₀ hα₀ fD hfDK w₀ hw₀ s k hk
        (Ws46.MidT1.measurableSet_yShell v k) n
    have htail := Ws1.Middle.DualGlue.htail_of_tail_eq v hπ V ℓ χD fD w₀ α₀ s (fun k hk n =>
      Ws46.MidT2.dualCell_tail_eq hπ hϖ V hVdK ℓ χD hχDu α₀ hα₀ α₁ hα₁ fD hfD hfDK w₀ hw₀ s k hk
        (Ws46.MidT1.measurableSet_yShell v k) n)

    have h4 := LanglandsTunnell.RankinSelberg.integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
      v (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) χD fD hfD w₀ hw₀ (1 - s) μ₂ (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) hI
    have hint := fun n : ℤ => SlMID.integrable_fibre_lattice_of_integrable4 v hπ hϖ (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) hK χD fD w₀ hfne (1 - s) h4 n

    have hcore : ∀ n : ℤ, N₀ ≤ n →
        localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n)))) * Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * D₀₁.eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) =
          ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) * ((dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ^ ℓ)⁻¹ * E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * ((((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n)⁻¹ *
            ((((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) * ((dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) ^ N₀ * (row₀ (n - N₀).toNat).eval (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s))) := by
      intro n hn
      obtain ⟨σn, hconv, hid⟩ := Ws1.Middle.Cells.localZeta31_dualTwist_lattice_eq ψv hψinv W hW hsm ωv hω hπ hϖ E Ed hE hEd ε ℓ h31 V hVmem hVK
        a₁ a₂ ha u χD hχDu hα₁' N₀ D₀₁ D₀₂ P₀ r₀ hTD₀ row₀ hrow₀ n hn
      have key := SlMID.dual_T2core_at v hπ hϖ (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (hχDu 1)
        (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) ε ((((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n) (((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ)
        (Ws1.Middle.DualGlue.dualAlpha1_ne_zero v _ hA1) hA1 E Ed D₀₁ (row₀ (n - N₀).toNat) ℓ N₀ σn hconv
        (fun s hs => by have h := hid s hs; simp only [dualX] at h; exact h) s (hint n)
      simp only [dualX]
      exact key
    have hcore₀ : ∀ n : ℤ, n < N₀ → localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n)))) = 0 := by
      intro n hn
      obtain ⟨σn, hconv, hid⟩ := Ws1.Middle.Cells.localZeta31_dualTwist_lattice_eq_zero ψv hψinv W hW hsm ωv hω hπ hϖ E Ed hE hEd ε ℓ h31 V hVmem hVK
        a₁ a₂ ha u χD hχDu hα₁' N₀ D₀₁ D₀₂ P₀ r₀ hTD₀ row₀ hrow₀ n hn
      exact SlMID.dual_T2core₀_at v hπ hϖ (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (hχDu 1)
        (iotaGL (diagUnits2 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n))) σn hconv hid s (hint n)

    have hX0 := Ws1.Middle.DualGlue.dualX_ne_zero v _ (Ws1.Middle.DualGlue.dualAlpha1_ne_zero v _ hA1) s
    have hY0 := Ws1.Middle.DualGlue.dualY_ne_zero v _ _ (Ws1.Middle.DualGlue.dualAlpha0_ne_zero v _ hA2) hω0 s
    have hres := hresum₀ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) (hσY s hsY)
    have hND := Ws1.Middle.DualGlue.numDen_eq v hπ V hVK ℓ N₀ D₀₁ D₀₂ P₀ r₀ hTD₀ Nt Dt₁ Dt₂ Pt rt hTDt _ _ hX0 hY0
    exact Ws1.Middle.DualGlue.S1_of_cells v hπ hϖ V ℓ χD fD w₀ ωv E Ed ε a₁ a₂ u ha cK α₀ hαa.1 hfD1
      N₀ D₀₁ D₀₂ P₀ Nt Dt₁ Dt₂ Pt row₀ s hT1 hbulk htail hcore hcore₀ hres hND
  obtain ⟨σt, hS1⟩ := S1

  have S2 : ∃ (m₁d m₂d : Polynomial ℂ) (kd : ℤ) (M : ℕ), m₂d ≠ 0 ∧
      (∀ s : ℂ, m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
        ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ M *
          (torusDen D₀₁ D₀₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen Dt₁ Dt₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * dualWtD v s)) ∧
      (∀ s : ℂ, m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s) =
        ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ M * (dualCNum v E Ed ε ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (dualC0 v ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ)) s *
          (torusNum N₀ P₀ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen Dt₁ Dt₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * dualWtD v s +
            dualWtN v s * torusNum Nt Pt (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen D₀₁ D₀₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s)))) := by
    have hq1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hqc : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    have ha12 : (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) ≠ 0 ∧ (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) ≠ 0 := by
      have hq' : ∀ z : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ z ≠ 0 := fun z => by
        rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hqc
      refine ⟨mul_ne_zero (left_ne_zero_of_mul ha) (hq' _), mul_ne_zero (right_ne_zero_of_mul ha) (hq' _)⟩
    have hA1 : dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) ≠ 0 := by
      unfold dualAlpha1
      refine mul_ne_zero ?_ (inv_ne_zero ha12.1)
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hqc
    have hA0 : dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) ≠ 0 := by
      unfold dualAlpha0
      refine mul_ne_zero ?_ (inv_ne_zero ha12.2)
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hqc
    have hωϖ : ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h := Ws1.Middle.Laurent1.example_dualNF (q := Ideal.absNorm v.asIdeal) hq1
      (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)
      (dualC0 v ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ)) ε (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) hA0 hA1 hωϖ
      ℓ E Ed D₀₁ D₀₂ Dt₁ Dt₂ P₀ Pt N₀ Nt hD₀₁ hD₀₂ hDt₁ hDt₂
    simp only [torusNum, torusDen, dualX, dualY, dualWtN, dualWtD, dualCNum]
    exact h
  obtain ⟨m₁d, m₂d, kd, M, hm₂d, hm₂, hm₁⟩ := S2

  refine ⟨m₁d, m₂d, kd, σt, hm₂d, ?_, fun s hs => ?_⟩
  ·
    intro Nb Db₁ Db₂ Pb rb hb Nt' Dt₁' Dt₂' Pt' rt' ht s
    have hqc : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    have hq' : ∀ z : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ z ≠ 0 := fun z => by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hqc
    have hX : dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s ≠ 0 := by
      unfold dualX dualAlpha1
      exact mul_ne_zero (inv_ne_zero (mul_ne_zero (hq' _) (inv_ne_zero (mul_ne_zero (left_ne_zero_of_mul ha) (hq' _))))) (hq' _)
    have hY : dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s ≠ 0 := by
      unfold dualY dualAlpha0
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hq' _) (inv_ne_zero (mul_ne_zero (right_ne_zero_of_mul ha) (hq' _)))) (inv_ne_zero (Units.ne_zero _))) (hq' _)
    have Ub := torusDatum_unique v hπ _ N₀ D₀₁ D₀₂ P₀ r₀ Nb Db₁ Db₂ Pb rb hTD₀ hb _ _ hX hY
    have Ut := torusDatum_unique v hπ _ Nt Dt₁ Dt₂ Pt rt Nt' Dt₁' Dt₂' Pt' rt' hTDt ht _ _ hX hY
    rw [hm₁ s, hm₂ s]
    linear_combination
      (((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ M * dualCNum v E Ed ε ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (dualC0 v ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ)) s *
          torusDen Dt₁ Dt₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen Dt₁' Dt₂' (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * dualWtD v s * dualWtD v s) * Ub +
      (((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ M * dualCNum v E Ed ε ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (dualC0 v ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ)) s * dualWtN v s * dualWtD v s *
          torusDen D₀₁ D₀₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s) * torusDen Db₁ Db₂ (dualX v (dualAlpha1 v (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))) s) (dualY v (dualAlpha0 v (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) s)) * Ut
  · have h := hS1 s hs
    have h2 := hm₂ s
    have h1 := hm₁ s
    linear_combination ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ M * h +
      (((cK : ℂ) * ∫ y, fD (w₀ * unipotentGL2 y) *
            (∫ a, ((χD 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1) *
              localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 a * unipotentGL2 y))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)) *
          Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) * h2 - h1

end Ws1.Middle
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

noncomputable section
namespace Ws1
namespace Middle
p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp"

theorem dual_half
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) :
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∀ (cK : ℝ) (_hcK : 0 < cK)
      (_hK1 : ∀ (θ : AddChar (v.adicCompletion ℚ) ℂ)
          (W : LocalGL3 v → ℂ) (_hW : IsGL3PsiWhittakerFn θ W)
          (_hWsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
          (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
          (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (_hf : f ∈ principalSeries2 v χ)
          (w₀ : GL (Fin 2) (v.adicCompletion ℚ))
          (_hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
          (s : ℂ),
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * f (w₀ * g)) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2)) μ₂ →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * (∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂(selfDualHaarAt ℚ v))) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W (iotaGL g)) (fun g => ∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂(selfDualHaarAt ℚ v)) =
            (cK : ℂ) * ∫ y, f (w₀ * unipotentGL2 y) *
              (∫ a, ((χ 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) *
                localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W (χ 1) s (iotaGL (diagUnits2 1 a * unipotentGL2 y)) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)),
      ∀ u : ℂ, ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) < ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re →
      ∀ (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)))
        ((Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u))) m),
      ∃ (m₁d m₂d : Polynomial ℂ) (kd : ℤ) (σD : ℝ), m₂d ≠ 0 ∧
      IsDualMiddleDatum v hπ V E Ed ε ℓ (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)
        (cK : ℂ) (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ)
        ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) m₁d m₂d kd ∧
      (∀ s : ℂ, σD < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (V) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s)) := by
  intro μ₂ _ μN _ cK hcK hK1 u hu W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT
  letI := localBorel ℚ v
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v

  have hVlaw : IsGL3PsiWhittakerFn ψv V := Ws1.Middle.DualKit.law_of_mem_gl3CyclicSubspace hW hVmem
  have hVsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, V (g * k) = V g := Ws1.Middle.DualKit.smooth_of_mem_gl3CyclicSubspace hsm hVmem
  have hD1law : IsGL3PsiWhittakerFn ψv⁻¹ (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) :=
    Ws1.Middle.DualKit.isGL3PsiWhittakerFn_rightTranslate
      (Ws1.Middle.DualKit.isGL3PsiWhittakerFn_inv_dualWhittakerFn3 hVlaw) _
  have hD1sm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (g * k) = (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) g :=
    Ws1.Middle.DualKit.smooth_rightTranslate (Ws1.Middle.DualKit.smooth_dualWhittakerFn3 hVsm) _

  have hD2 : ∃ (α₀ α₁ : ℂ) (_ : α₀ ≠ 0 ∧ α₁ ≠ 0) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
      (_ : ∀ i, ∀ e : (v.adicCompletion ℚ)ˣ, Valued.v (e : v.adicCompletion ℚ) = 1 → χD i e = 1)
      (_ : ((χD 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₀) (_ : ((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) = α₁)
      (_ : α₀ * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) ∧ α₁ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2))
      (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (_ : fD ∈ principalSeries2 v χD)
      (_ : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → fD (g * k) = fD g)
      (_ : fD 1 = ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹)
      (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (_ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0]),
      W₂d = fun g => ∫ y, fD (w₀ * unipotentGL2 y * g) * ψv⁻¹ y ∂(selfDualHaarAt ℚ v) :=
    Ws1.Middle.DualD23.sectionRep_dual v hπ hϖ ψv hψinv a₁ a₂ ha u hu W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT
  obtain ⟨α₀, α₁, hα, χD, hχDu, hα₀, hα₁, hαa, fD, hfD, hfDK, hfD1, w₀, hw₀, rfl⟩ := hD2

  have hdom : ‖((χD 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)‖ < ‖((χD 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)‖ := by
    rw [hα₀, hα₁]; exact Ws1.Middle.DualD23.dominance_of_alpha_eq v a₁ a₂ ha u hu α₀ α₁ hαa
  have hD3 : ∃ σc : ℝ, ∀ s : ℂ, σc < (1 - s).re →
      Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
        ((fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (iotaGL g) * fD (w₀ * g)) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
            ((1 - s) - 1 / 2)) μ₂ :=
    Ws1.Middle.DualD23.integrable_sectionForm_dual v hπ hϖ (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) hD1sm
      (Ws1.Middle.DualD23.gauge_dual_rightTranslate v W hWgauge V hVmem (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))))
      χD hχDu hdom fD hfD hfDK w₀ hw₀ μ₂
  obtain ⟨σc, hσc⟩ := hD3

  have hD4 := fun (s : ℂ) (hs : σc < (1 - s).re) =>
    (hK1 ψv⁻¹ (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) hD1law hD1sm χD fD hfD w₀ hw₀ (1 - s) (hσc s hs)).2

  obtain ⟨hE, hEd⟩ :=
    LanglandsTunnell.CubicInduction.ne_zero_and_ne_zero_of_forall_localZeta30_eq_inv_eval_mul_and_localZetaDual31_eq_inv_eval_mul
      v W (hψinv ▸ hW) (fun h0 => by simpa [h0] using hW1) hirr hsm E Ed ε ℓ h31
  obtain ⟨m₁d, m₂d, kd, σt, hm₂d, hDd, ht⟩ :=
    dual_transport v ψv hψinv W hW hW1 hmult hirr hsm hadm hWgauge ωv hωu hω hπ hϖ E Ed ε ℓ h31 hE hEd V hVmem hVK hVdK a₁ a₂ ha μ₂ μN cK hcK u hu
      α₀ α₁ hα χD hχDu hα₀ hα₁ hαa fD hfD hfDK hfD1 w₀ hw₀ σc hσc
  refine ⟨m₁d, m₂d, kd, max σc σt, hm₂d, hDd, fun s hs => ?_⟩
  have hs₁ : σc < (1 - s).re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs₂ : σt < (1 - s).re := lt_of_le_of_lt (le_max_right _ _) hs
  rw [hD4 s hs₁]
  exact ht s hs₂

end Ws1.Middle
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

noncomputable section
p2m_open "IsDedekindDomain NumberField AutomorphicForm~lowerUnipotentGL2 LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) :
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∀ (cK : ℝ) (_hcK : 0 < cK)
      (_hK1 : ∀ (θ : AddChar (v.adicCompletion ℚ) ℂ)
          (W : LocalGL3 v → ℂ) (_hW : IsGL3PsiWhittakerFn θ W)
          (_hWsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
          (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
          (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (_hf : f ∈ principalSeries2 v χ)
          (w₀ : GL (Fin 2) (v.adicCompletion ℚ))
          (_hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
          (s : ℂ),
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * f (w₀ * g)) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2)) μ₂ →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * (∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂(selfDualHaarAt ℚ v))) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W (iotaGL g)) (fun g => ∫ y, f (w₀ * unipotentGL2 y * g) * θ y ∂(selfDualHaarAt ℚ v)) =
            (cK : ℂ) * ∫ y, f (w₀ * unipotentGL2 y) *
              (∫ a, ((χ 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) *
                localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W (χ 1) s (iotaGL (diagUnits2 1 a * unipotentGL2 y)) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) ∂(selfDualHaarAt ℚ v)),
      ∀ u : ℂ, ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) < ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re →
      ∀ (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)))
        ((Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u))) m),
      ∃ (m₁d m₂d : Polynomial ℂ) (kd : ℤ) (σD : ℝ), m₂d ≠ 0 ∧
      (
      ∀ (Nb : ℤ) (Db₁ Db₂ : Polynomial ℂ) (Pb : MvPolynomial (Fin 2) ℂ) (rb : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Db₁.eval 0 ≠ 0 ∧ Db₂.eval 0 ≠ 0 ∧ 0 < rb ∧
          (∀ n : ℤ × ℤ, (n.1 < Nb ∨ n.2 < Nb) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rb → ‖Y‖ < rb →
            Summable (fun m : ℕ × ℕ => ‖A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Db₁.eval X * Db₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pb)
        ) →
      ∀ (Nt : ℤ) (Dt₁ Dt₂ : Polynomial ℂ) (Pt : MvPolynomial (Fin 2) ℂ) (rt : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Dt₁.eval 0 ≠ 0 ∧ Dt₂.eval 0 ≠ 0 ∧ 0 < rt ∧
          (∀ n : ℤ × ℤ, (n.1 < Nt ∨ n.2 < Nt) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rt → ‖Y‖ < rt →
            Summable (fun m : ℕ × ℕ => ‖A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Dt₁.eval X * Dt₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pt)
        ) →
      ∀ s : ℂ,
        m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s) *
            ((Db₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (Dt₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹)) =
          m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹ * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹) ^ ℓ)⁻¹) * ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) *
            (((((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nb * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nb * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pb) * (Dt₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) +
              ((1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nt * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nt * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pt) * (Db₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)))) ∧
      (∀ s : ℂ, σD < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (V) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s)) :=
  Ws1.Middle.dual_half v ψv hψinv W hW hW1 hmult hirr hsm hadm hWgauge ωv hωu hω hπ hϖ E Ed ε ℓ h31 V hVmem hVK hVdK a₁ a₂ ha
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualKit P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws1.Middle.DualD23 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT1 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.Ws46.MidT2 P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant.SlMID"

end
end
end
end
end
end S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant (solution)
