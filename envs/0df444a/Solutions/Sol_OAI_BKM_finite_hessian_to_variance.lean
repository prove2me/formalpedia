-- Prove2me | solution 1 for OAI.BKM.finite_hessian_to_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:35:27.191944+00:00
-- url     : https://prove2.me/submissions/4d724bcf-76a2-4d90-af9b-8fc1dc269116

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/SpectralForms.lean:L119-L136
-- (upload_full_project.md Phase 4): solution for node OAI.BKM.finite_hessian_to_variance. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms

-- ---- from OAI.InformationTheory.PhotonNumber.SpectralForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

namespace BKM

section
open scoped ComplexConjugate
variable {J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

open scoped BigOperators
variable {J : Type*}

 theorem tendsto_square_finset : Tendsto (fun s : Finset J => s ×ˢ s) atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro t
  filter_upwards [eventually_ge_atTop (t.image Prod.fst ∪ t.image Prod.snd)] with s hs
  intro ij hij
  exact Finset.mem_product.mpr ⟨hs (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ij,hij,rfl⟩)),
    hs (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ij,hij,rfl⟩))⟩

 theorem hasSum_square_finset {v : J × J → ℝ} {a : ℝ} (h : HasSum v a) :
    Tendsto (fun s : Finset J => ∑ i ∈ s, ∑ j ∈ s, v (i,j)) atTop (𝓝 a) := by
  classical
  simpa only [Function.comp_def, Finset.sum_product] using h.comp tendsto_square_finset

 theorem finite_hessian_to_variance (v : J × J → ℝ) (m : J → ℝ) (μ A α γ W : ℝ)
    (hv : HasSum v A) (hm : HasSum m μ) (hα : 0 < α)
    (h : ∀ (s : Finset J) (t : ℝ),
      2*γ*t*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-μ*(∑ i ∈ s, m i)) ≤
        α*t^2*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-(∑ i ∈ s, m i)^2)+W) :
    γ^2*(A-μ^2) ≤ α*W := by
  have hQ := hasSum_square_finset hv
  have hlo : Tendsto (fun s : Finset J =>
      2*γ*(γ/α)*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-μ*(∑ i ∈ s, m i))) atTop
        (𝓝 (2*γ*(γ/α)*(A-μ*μ))) := (hQ.sub (hm.const_mul μ)).const_mul _
  have hup : Tendsto (fun s : Finset J =>
      α*(γ/α)^2*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-(∑ i ∈ s, m i)^2)+W) atTop
        (𝓝 (α*(γ/α)^2*(A-μ^2)+W)) := ((hQ.sub (hm.pow 2)).const_mul _).add_const _
  have hh := le_of_tendsto_of_tendsto hlo hup (Filter.Eventually.of_forall fun s => h s (γ/α))
  have hh' := mul_le_mul_of_nonneg_left hh hα.le
  have hne := hα.ne'
  field_simp at hh'
  nlinarith

end BKM

namespace SpectralTests
open scoped BigOperators ComplexConjugate
variable {A I P : Type*}

end SpectralTests

namespace CenteredTests
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [CompleteSpace E]

end CenteredTests

namespace ThermalMetric

section
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open scoped ComplexConjugate
variable {J : Type*}

variable [DecidableEq J]

end

open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalMetric

end

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
open Filter Topology

namespace CenteredTests
open scoped BigOperators
variable {J T E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CenteredTests

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

end ThermalMetric

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace Space
variable (S : Space E)
end Space

end ThermalSpectral

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

end ThermalMetric

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation BeamLadder ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace ThermalSpectral.Space
open EntropyPhotonNumber Annihilation WeightedGenerator ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} (S : Space (Fock n))

end ThermalSpectral.Space

end

end OAI

-- ---- platform node ----
open OAI OAI.BKM
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
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.BKM.finite_hessian_to_variance := @_root_.OAI.BKM.finite_hessian_to_variance
