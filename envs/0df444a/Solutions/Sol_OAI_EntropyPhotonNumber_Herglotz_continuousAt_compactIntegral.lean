-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Herglotz.continuousAt_compactIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:22:59.24758+00:00
-- url     : https://prove2.me/submissions/8905f20f-0150-40e5-9dd6-90089adc2cc2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean:L982-L1012
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Herglotz.continuousAt_compactIntegral. The node keeps its source
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

theorem continuousAt_compactIntegral (μ : FiniteMeasure Angle) {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (compactIntegral μ) s := by
  let d : ℝ := min 1 (s.re / 2)
  have hd : 0 < d := lt_min zero_lt_one (half_pos hs)
  apply continuousAt_of_dominated (bound := fun _ => 1 / d)
  · filter_upwards with z
    have hm : Measurable (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) z) :=
      (Complex.continuous_ofReal.comp continuous_boundaryWeight).measurable.div
        (continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter))).measurable
    exact hm.aestronglyMeasurable
  · have he : ∀ᶠ z : ℂ in 𝓝 s, s.re / 2 < z.re :=
      (Complex.continuous_re.continuousAt.tendsto).eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [he] with z hz
    filter_upwards with θ
    have ht := boundaryParameter_mem θ
    have hd1 : d ≤ 1 := min_le_left _ _
    have hdz : d ≤ z.re := (min_le_right _ _).trans hz.le
    have hdr : d ≤ (1 + (z - 1) * (boundaryParameter θ : ℂ)).re := by
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.sub_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr ht.2),
        mul_nonneg (sub_nonneg.mpr hdz) ht.1]
    have hdn : d ≤ ‖1 + (z - 1) * (boundaryParameter θ : ℂ)‖ := hdr.trans (Complex.re_le_norm _)
    rw [compactKernel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (boundaryWeight_pos θ)]
    exact div_le_div₀ zero_le_one (boundaryWeight_le_one θ) hd hdn
  · exact integrable_const _
  · filter_upwards with θ
    exact continuousAt_const.div
      (continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul continuousAt_const))
      (compactDen_ne_zero (boundaryParameter_mem θ) (Or.inr hs))

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


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Herglotz.continuousAt_compactIntegral := @_root_.OAI.EntropyPhotonNumber.Herglotz.continuousAt_compactIntegral
