-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Herglotz.differentiableAt_compactIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:25:55.025828+00:00
-- url     : https://prove2.me/submissions/6f7cc7da-7468-40a0-a0c7-6197d8634e02

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean:L1248-L1292
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Herglotz.differentiableAt_compactIntegral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compactDen_ne_zero

-- ---- from OAI.Analysis.Herglotz ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber.Herglotz

section Density
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

end Density

section WeakIntegral
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X]

end WeakIntegral

attribute [local instance] OAI.EntropyPhotonNumber.Herglotz.instMeasureSpaceElemRealAngle
theorem boundaryWeight_pos (θ : Angle) : 0 < boundaryWeight θ := by
  dsimp [boundaryWeight]
  positivity

theorem boundaryWeight_le_one (θ : Angle) : boundaryWeight θ ≤ 1 := by
  dsimp [boundaryWeight]
  exact inv_le_one_of_one_le₀ (by linarith [le_max_left 0 (circleMap 0 1 θ).im])

theorem compactKernel_integrable (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) :
    Integrable (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s)
      (μ : Measure Angle) := by
  have hc : Continuous (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s) := by
    exact (Complex.continuous_ofReal.comp continuous_boundaryWeight).div
      (continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp continuous_boundaryParameter)))
      (fun θ => compactDen_ne_zero (boundaryParameter_mem θ) hs)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem compactDen_loc_lower {s : ℂ} (hs : 0 < s.im ∨ 0 < s.re) :
    ∃ d : ℝ, 0 < d ∧ ∀ z ∈ ball s d, ∀ θ : Angle,
      d ≤ ‖1 + (z - 1) * (boundaryParameter θ : ℂ)‖ := by
  let D : ℂ → Angle → ℂ := fun z θ => 1 + (z - 1) * (boundaryParameter θ : ℂ)
  have hc : Continuous (fun θ : Angle => ‖D s θ‖) :=
    (continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_boundaryParameter))).norm
  have hne : (univ : Set Angle).Nonempty := ⟨⟨0, le_rfl, by positivity⟩, mem_univ _⟩
  obtain ⟨θ₀, _, hmin⟩ := isCompact_univ.exists_isMinOn hne hc.continuousOn
  have hp : 0 < ‖D s θ₀‖ := norm_pos_iff.mpr (compactDen_ne_zero (boundaryParameter_mem θ₀) hs)
  refine ⟨‖D s θ₀‖ / 2, half_pos hp, ?_⟩
  intro z hz θ
  have hlow : ‖D s θ₀‖ ≤ ‖D s θ‖ := hmin (mem_univ θ)
  have ht : ‖(boundaryParameter θ : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (boundaryParameter_mem θ).1]
      using (boundaryParameter_mem θ).2
  have hdiff : ‖D s θ - D z θ‖ ≤ ‖s - z‖ := by
    have he : D s θ - D z θ = (s - z) * (boundaryParameter θ : ℂ) := by dsimp [D]; ring
    rw [he, norm_mul]
    exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_one _)
  have hnorm := norm_sub_norm_le (D s θ) (D z θ)
  have hnear : ‖s - z‖ < ‖D s θ₀‖ / 2 := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hz
  change ‖D s θ₀‖ / 2 ≤ ‖D z θ‖
  linarith

theorem hasDerivAt_compactKernel {t w : ℝ} {z : ℂ}
    (hn : 1 + (z - 1) * (t : ℂ) ≠ 0) :
    HasDerivAt (compactKernel t w)
      (-((w : ℂ) * t) / (1 + (z - 1) * (t : ℂ)) ^ 2) z := by
  have hd : HasDerivAt (fun s : ℂ => 1 + (s - 1) * (t : ℂ)) (t : ℂ) z := by
    simpa only [id_eq, one_mul] using (((hasDerivAt_id z).sub_const 1).mul_const (t : ℂ)).const_add 1
  convert! (hasDerivAt_const z (w : ℂ)).div hd hn using 1
  simp only [zero_mul, zero_sub]

theorem differentiableAt_compactIntegral (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : DifferentiableAt ℂ (compactIntegral μ) s := by
  obtain ⟨d, hd, hden⟩ := compactDen_loc_lower hs
  let F' : ℂ → Angle → ℂ := fun z θ =>
    -((boundaryWeight θ : ℂ) * boundaryParameter θ) /
      (1 + (z - 1) * (boundaryParameter θ : ℂ)) ^ 2
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable
      (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) z) (μ : Measure Angle) := by
    intro z
    have hm : Measurable (fun θ : Angle => compactKernel (boundaryParameter θ) (boundaryWeight θ) z) := by
      unfold compactKernel
      exact (Complex.continuous_ofReal.comp continuous_boundaryWeight).measurable.div
        (continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter))).measurable
    exact hm.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' s) (μ : Measure Angle) := by
    have hm : Measurable (F' s) := by
      dsimp [F']
      apply Measurable.div
      · exact ((Complex.continuous_ofReal.comp continuous_boundaryWeight).mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter)).neg.measurable
      · exact ((continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter))).pow 2).measurable
    exact hm.aestronglyMeasurable
  have hbound : ∀ᵐ θ : Angle ∂(μ : Measure Angle), ∀ z ∈ ball s d, ‖F' z θ‖ ≤ 1 / d ^ 2 := by
    filter_upwards with θ z hz
    have ht := boundaryParameter_mem θ
    have hw := boundaryWeight_le_one θ
    have hp := boundaryWeight_pos θ
    have hnum : ‖(boundaryWeight θ : ℂ) * boundaryParameter θ‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ht.1, abs_of_pos hp]
      exact (mul_le_mul hw ht.2 ht.1 zero_le_one).trans_eq (one_mul 1)
    dsimp [F']
    rw [norm_div, norm_neg, norm_pow]
    exact div_le_div₀ zero_le_one hnum (sq_pos_of_pos hd)
      (sq_le_sq₀ hd.le (norm_nonneg _) |>.mpr (hden z hz θ))
  have hdiff : ∀ᵐ θ : Angle ∂(μ : Measure Angle), ∀ z ∈ ball s d,
      HasDerivAt (fun u => compactKernel (boundaryParameter θ) (boundaryWeight θ) u) (F' z θ) z := by
    filter_upwards with θ z hz
    apply hasDerivAt_compactKernel
    exact norm_pos_iff.mp (hd.trans_le (hden z hz θ))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds s hd)
    (Eventually.of_forall hmeas) (compactKernel_integrable μ hs) hmeas' hbound
      (integrable_const (1 / d ^ 2)) hdiff).2.differentiableAt

end EntropyPhotonNumber.Herglotz

end

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Herglotz
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
attribute [local instance] OAI.EntropyPhotonNumber.Herglotz.instMeasureSpaceElemRealAngle


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Herglotz.differentiableAt_compactIntegral := @_root_.OAI.EntropyPhotonNumber.Herglotz.differentiableAt_compactIntegral
