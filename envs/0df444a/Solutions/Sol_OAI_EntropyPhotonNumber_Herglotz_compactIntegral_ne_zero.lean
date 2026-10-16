-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Herglotz.compactIntegral_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:21:24.130549+00:00
-- url     : https://prove2.me/submissions/f474a3a6-62db-4024-91e6-71d1ab110617

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean:L948-L980
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Herglotz.compactIntegral_ne_zero. The node keeps its source
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

theorem compactKernel_im (t w : ℝ) (s : ℂ) :
    (compactKernel t w s).im = -(w * t * s.im) / Complex.normSq (1 + (s - 1) * t) := by
  simp only [compactKernel, Complex.div_im, Complex.ofReal_im, zero_mul,
    Complex.ofReal_re, Complex.add_im, Complex.one_im, Complex.mul_im,
    Complex.sub_im, sub_zero, mul_zero, zero_add]
  ring

theorem mul_compactKernel_im (t w : ℝ) (s : ℂ) :
    (s * compactKernel t w s).im = w * (1 - t) * s.im / Complex.normSq (1 + (s - 1) * t) := by
  rw [compactKernel, ← mul_div_assoc, Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_im, Complex.one_re, sub_zero, mul_zero, zero_add]
  ring

theorem complex_im_integral {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → ℂ} (hf : Integrable f ν) : (∫ x, f x ∂ν).im = ∫ x, (f x).im ∂ν :=
  (Complex.imCLM.integral_comp_comm hf).symm

theorem compactIntegral_ne_zero (μ : FiniteMeasure Angle)
    (hμ : (μ : Measure Angle) ≠ 0) {s : ℂ} (hs : 0 < s.im) : compactIntegral μ s ≠ 0 := by
  let F : Angle → ℝ := fun θ => (s * compactKernel (boundaryParameter θ) (boundaryWeight θ) s).im -
    (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).im
  have hF (θ : Angle) : 0 < F θ := by
    dsimp [F]
    rw [mul_compactKernel_im, compactKernel_im]
    have he : boundaryWeight θ * (1 - boundaryParameter θ) * s.im - -(boundaryWeight θ * boundaryParameter θ * s.im) =
        boundaryWeight θ * s.im := by ring
    rw [← sub_div, he]
    exact div_pos (mul_pos (boundaryWeight_pos θ) hs)
      (Complex.normSq_pos.mpr (compactDen_ne_zero (boundaryParameter_mem θ) (Or.inl hs)))
  have hi := compactKernel_integrable μ (Or.inl hs)
  have hFi : Integrable F (μ : Measure Angle) :=
    (Complex.imCLM.integrable_comp (hi.const_mul s)).sub (Complex.imCLM.integrable_comp hi)
  have hp : 0 < ∫ θ, F θ ∂(μ : Measure Angle) := by
    rw [integral_pos_iff_support_of_nonneg (fun θ => (hF θ).le) hFi]
    have he : Function.support F = univ := by ext θ; simp [Function.mem_support, (hF θ).ne']
    rw [he]
    exact Measure.measure_univ_pos.mpr hμ
  have he : (∫ θ, F θ ∂(μ : Measure Angle)) =
      (s * compactIntegral μ s).im - (compactIntegral μ s).im := by
    have hi₁ : Integrable (fun θ => (s * compactKernel (boundaryParameter θ) (boundaryWeight θ) s).im)
        (μ : Measure Angle) := Complex.imCLM.integrable_comp (hi.const_mul s)
    have hi₂ : Integrable (fun θ => (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).im)
        (μ : Measure Angle) := Complex.imCLM.integrable_comp hi
    dsimp [F]
    rw [integral_sub hi₁ hi₂, ← complex_im_integral (hi.const_mul s), ← complex_im_integral hi,
      integral_const_mul]
    rfl
  intro hz
  rw [he, hz, mul_zero, Complex.zero_im, sub_self] at hp
  exact lt_irrefl _ hp

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


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Herglotz.compactIntegral_ne_zero := @_root_.OAI.EntropyPhotonNumber.Herglotz.compactIntegral_ne_zero
