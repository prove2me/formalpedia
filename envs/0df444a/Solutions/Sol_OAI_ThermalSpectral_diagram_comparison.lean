-- Prove2me | solution 1 for OAI.ThermalSpectral.diagram_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:36:47.024186+00:00
-- url     : https://prove2.me/submissions/ea8ea73f-4d29-459c-ad2e-54fba110f205

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/SpectralForms.lean:L735-L767
-- (upload_full_project.md Phase 4): solution for node OAI.ThermalSpectral.diagram_comparison. The node keeps its source
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

omit [CompleteSpace E] in
theorem realize_entries (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ)
    (hw : ∀ ij, 0 < w ij) (z : coordinates b p w) : entryMap b w (realize b p w hw z)=z.val := by
  exact LinearEquiv.ofInjective_symm_apply (h := entryMap_injective b w hw) _ _

omit [CompleteSpace E] in
theorem realize_mem (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ)
    (hw : ∀ ij, 0 < w ij) (z : coordinates b p w) : realize b p w hw z ∈ operatorSpace b p := by
  obtain ⟨Z,hZ,he⟩ := z.property
  have hh : realize b p w hw z=Z := entryMap_injective b w hw ((realize_entries b p w hw z).trans he.symm)
  rw [hh]
  exact hZ

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
theorem base_pos (ij : S.I × S.I) : 0 < S.base ij := mul_pos (h_pos S.rpos) (logMean_pos (S.pos _) (S.pos _))
end Space

theorem targetMap_norm (S : Fin 2 → Space E) (w : Fin 2 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (Z : E →L[ℂ] E) (a : Σ i, (S i).I × (S i).I) :
    Complex.normSq (targetMap S w L Z a)=w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2) := by
  simp only [targetMap, LinearMap.coe_mk, AddHom.coe_mk, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (hw _)]

theorem diagram_comparison (S₀ : Space E) (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) (X : Param → ℝ)
    (hX : ∀ q, 0 ≤ X q)
    (hs : ∀ i Z, Summable (fun a => X ((S i).pparam a)*Complex.normSq ((S i).coords Z a)))
    (he : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      ∑ i, w i*(S i).pquad X (L i Z) ≤ S₀.pquad X Z) :
    (diagram S₀ S w L).Comparison X := by
  intro z s
  let Z := CenteredTests.realize S₀.basis S₀.p S₀.base S₀.base_pos z
  have hz : S₀.coords Z=z.val := CenteredTests.realize_entries S₀.basis S₀.p S₀.base S₀.base_pos z
  have hm : Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p :=
    CenteredTests.realize_mem S₀.basis S₀.p S₀.base S₀.base_pos z
  have hn (a : Σ i, (S i).I × (S i).I) : 0 ≤ X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2)) := mul_nonneg (hX _) (mul_nonneg (hw _) (Complex.normSq_nonneg _))
  have hsum : Summable (fun a : Σ i, (S i).I × (S i).I => X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2))) := by
    apply (summable_sigma_of_nonneg hn).mpr
    refine ⟨fun i => ?_, (hasSum_fintype _).summable⟩
    simpa only [mul_left_comm] using (hs i (L i Z)).mul_left (w i)
  have ht := Summable.sum_le_tsum s (fun a _ => hn a) hsum
  have hv : (∑' a : Σ i, (S i).I × (S i).I, X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2))) =
      ∑ i, w i*(S i).pquad X (L i Z) := by
    rw [hsum.tsum_sigma]
    simp only [tsum_fintype, Space.pquad, mul_left_comm (X _) (w _), tsum_mul_left]
  rw [hv] at ht
  have hh := ht.trans (he Z hm)
  change (∑ a ∈ s, X ((S a.1).pparam a.2)*Complex.normSq (targetMap S w L Z a)) ≤ _
  simp only [targetMap_norm S w hw L]
  convert! hh using 1
  simp only [sourceForm, Space.pquad, hz]
  rfl

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
open OAI OAI.ThermalSpectral
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
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ThermalSpectral.diagram_comparison := @_root_.OAI.ThermalSpectral.diagram_comparison
