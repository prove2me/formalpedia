-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Herglotz.compactDen_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:17:56.524978+00:00
-- url     : https://prove2.me/submissions/6b78673d-015a-426d-8579-d9869198248a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean:L743-L759
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Herglotz.compactDen_ne_zero. The node keeps its source
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
theorem compactDen_ne_zero {t : ℝ} (ht : t ∈ Icc 0 1) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : 1 + (s - 1) * (t : ℂ) ≠ 0 := by
  intro he
  rcases hs with hs | hs
  · have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.sub_im,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re, zero_add,
      Complex.zero_im] at hi
    have ht0 : t = 0 := (mul_eq_zero.mp hi).resolve_left hs.ne'
    simp [ht0] at he
  · have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.sub_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re, Complex.zero_re] at hr
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
      intro h
      simp [← h] at he)
    nlinarith [mul_pos hs ht0, ht.2]

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


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Herglotz.compactDen_ne_zero := @_root_.OAI.EntropyPhotonNumber.Herglotz.compactDen_ne_zero
