-- Prove2me | solution 1 for OAI.QuantumTrace.tendsto_tsum_of_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:37:08.971838+00:00
-- url     : https://prove2.me/submissions/0b41e565-3d0c-47e1-9a0e-eb9a88e9cb6b

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L385-L416
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.tendsto_tsum_of_uniform_tail. The node keeps its source
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

-- ---- from OAI.InformationTheory.PhotonNumber.Entropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace Annihilation
open EntropyPhotonNumber QuantumTrace WeightedShift
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped BigOperators
variable {n : ℕ} {I : Type*}

end WeightedGenerator

namespace WeightedShift
variable {I K : Type*}
end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section
open Filter Topology

theorem tendsto_tsum_of_uniform_tail {α ι : Type*} {l : Filter α}
    {f : α → ι → ℝ} {g : ι → ℝ}
    (hf : ∀ a, Summable (f a)) (hg : Summable g)
    (hfp : ∀ a i, 0 ≤ f a i) (hgp : ∀ i, 0 ≤ g i)
    (hlim : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i)))
    (htail : ∀ ε > 0, ∃ s : Finset ι,
      (∀ a, (∑' i : {i // i ∉ s}, f a i) < ε) ∧
      (∑' i : {i // i ∉ s}, g i) < ε) :
    Tendsto (fun a => ∑' i, f a i) l (𝓝 (∑' i, g i)) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, hs, hsg⟩ := htail (ε / 3) (by positivity)
  have hh := Metric.tendsto_nhds.mp (tendsto_finsetSum s (fun i _ => hlim i)) (ε / 3) (by positivity)
  filter_upwards [hh] with a ha
  rw [dist_eq_norm, ← (hf a).sum_add_tsum_compl (s := s), ← hg.sum_add_tsum_compl (s := s)]
  have hsub :
      (∑ i ∈ s, f a i) + (∑' i : {i // i ∉ s}, f a i) -
      ((∑ i ∈ s, g i) + (∑' i : {i // i ∉ s}, g i)) =
      ((∑ i ∈ s, f a i) - (∑ i ∈ s, g i)) +
      ((∑' i : {i // i ∉ s}, f a i) - (∑' i : {i // i ∉ s}, g i)) := by ring
  change ‖(∑ i ∈ s, f a i) + (∑' i : {i // i ∉ s}, f a i) -
    ((∑ i ∈ s, g i) + (∑' i : {i // i ∉ s}, g i))‖ < ε
  rw [hsub]
  apply (norm_add_le _ _).trans_lt
  have hnorm := norm_sub_le (∑' i : {i // i ∉ s}, f a i) (∑' i : {i // i ∉ s}, g i)
  simp only [Real.norm_eq_abs] at hnorm
  rw [abs_of_nonneg (tsum_nonneg (fun i : {i // i ∉ s} => hfp a i)),
    abs_of_nonneg (tsum_nonneg (fun i : {i // i ∉ s} => hgp i))] at hnorm
  simp only [Real.norm_eq_abs]
  rw [dist_eq_norm, Real.norm_eq_abs] at ha
  linarith [hs a]

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end QuantumTrace

end

namespace EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal

namespace TraceEnsemble
open Filter Topology
open scoped BigOperators
variable {I A E G : Type*}
variable [NormedAddCommGroup G] [CompleteSpace G]

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end TraceEnsemble

namespace TensorLp
variable {A B : Type*}

end TensorLp

namespace EntropyPhotonNumber

section
open Filter Topology TensorLp

end

open QuantumTrace TraceEnsemble
end EntropyPhotonNumber

namespace QuantumTrace
open scoped ENNReal

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
end

open QuantumTrace Filter Topology

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

variable [CompleteSpace E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

end

open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {ι J L : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {J : Type*}

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology


theorem solution : type_of% @_root_.OAI.QuantumTrace.tendsto_tsum_of_uniform_tail := @_root_.OAI.QuantumTrace.tendsto_tsum_of_uniform_tail
