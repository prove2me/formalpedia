-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Herglotz.compactIntegral_real_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:27:30.921418+00:00
-- url     : https://prove2.me/submissions/698bce10-1abb-42de-9c0f-090edeabbcd1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean:L1305-L1317
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Herglotz.compactIntegral_real_pos. The node keeps its source
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

theorem integrable_realKernel (μ : FiniteMeasure Angle) {x : ℝ} (hx : 0 < x) :
    Integrable (fun θ => boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ)) (μ : Measure Angle) := by
  exact (continuous_boundaryWeight.div
    (continuous_const.add (continuous_const.mul continuous_boundaryParameter))
    (fun θ => (real_compactDen_pos (boundaryParameter_mem θ) hx).ne')).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem compactIntegral_real (μ : FiniteMeasure Angle) (x : ℝ) :
    compactIntegral μ (x : ℂ) =
      ((∫ θ : Angle, boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) ∂(μ : Measure Angle) : ℝ) : ℂ) := by
  rw [compactIntegral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with θ
  simp only [compactKernel, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem compactIntegral_real_pos (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    {x : ℝ} (hx : 0 < x) : 0 < (compactIntegral μ (x : ℂ)).re := by
  rw [compactIntegral_real, Complex.ofReal_re]
  have hp (θ : Angle) : 0 < boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) :=
    div_pos (boundaryWeight_pos θ) (real_compactDen_pos (boundaryParameter_mem θ) hx)
  rw [integral_pos_iff_support_of_nonneg (fun θ => (hp θ).le) (integrable_realKernel μ hx)]
  have he : Function.support (fun θ : Angle => boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ)) =
      univ := by
    ext θ
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp θ).ne'
  rw [he]
  exact Measure.measure_univ_pos.mpr hμ

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


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Herglotz.compactIntegral_real_pos := @_root_.OAI.EntropyPhotonNumber.Herglotz.compactIntegral_real_pos
