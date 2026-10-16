-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Herglotz.tendsto_integral_varying
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:16:36.555321+00:00
-- url     : https://prove2.me/submissions/318afad2-9069-491b-906b-93bad7999ae9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean:L56-L80
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Herglotz.tendsto_integral_varying. The node keeps its source
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

theorem tendsto_integral_varying {ι : Type*} {l : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    {fs : ι → C(X, ℝ)} {f : C(X, ℝ)}
    (hμ : Tendsto μs l (𝓝 μ)) (hf : Tendsto fs l (𝓝 f)) :
    Tendsto (fun i => ∫ x, fs i x ∂(μs i : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have hfixed := (FiniteMeasure.continuous_integral_continuousMap f).continuousAt.tendsto.comp hμ
  have hmass : Tendsto (fun i => ((μs i).mass : ℝ)) l (𝓝 (μ.mass : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      (FiniteMeasure.continuous_mass.continuousAt.tendsto.comp hμ)
  have hnorm : Tendsto (fun i => ‖fs i - f‖) l (𝓝 0) := by
    simpa using (hf.sub (tendsto_const_nhds (x := f))).norm
  have hdiff : Tendsto (fun i => ∫ x, (fs i - f) x ∂(μs i : Measure X)) l (𝓝 0) := by
    refine squeeze_zero_norm (fun i => ?_) (by simpa using hnorm.mul hmass)
    simpa only [FiniteMeasure.measureReal_eq_coe_coeFn, FiniteMeasure.mass] using
      (norm_integral_le_of_norm_le_const (μ := (μs i : Measure X))
        (Eventually.of_forall (fun x => (fs i - f).norm_coe_le_norm x)))
  have hi (i : ι) : (∫ x, (fs i - f) x ∂(μs i : Measure X)) =
      (∫ x, fs i x ∂(μs i : Measure X)) - ∫ x, f x ∂(μs i : Measure X) :=
    integral_sub
      ((fs i).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  simpa only [hi, Function.comp_apply, sub_add_cancel, zero_add] using hdiff.add hfixed

end WeakIntegral

attribute [local instance] OAI.EntropyPhotonNumber.Herglotz.instMeasureSpaceElemRealAngle
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


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Herglotz.tendsto_integral_varying := @_root_.OAI.EntropyPhotonNumber.Herglotz.tendsto_integral_varying
