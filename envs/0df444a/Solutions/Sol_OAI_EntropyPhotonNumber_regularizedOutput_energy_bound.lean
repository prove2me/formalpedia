-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.regularizedOutput_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:43:47.849348+00:00
-- url     : https://prove2.me/submissions/f57c1ebb-cd99-4c32-8d4f-1a334255650f

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L1240-L1256
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.regularizedOutput_energy_bound. The node keeps its source
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
theorem mixture_energy {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc 0 1) {ρ σ : State n}
    (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    energy (mixture t ht ρ σ) = t*energy ρ+(1-t)*energy σ := by
  unfold energy
  have he (k : NumberIndex n) :
      (totalNumber k : ℝ)*(entry (mixture t ht ρ σ).op k k).re =
      t*((totalNumber k : ℝ)*(entry ρ.op k k).re)+
        (1-t)*((totalNumber k : ℝ)*(entry σ.op k k).re) := by
    simp only [mixture_entry, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  simp only [he]
  rw [(hρ.mul_left t).tsum_add (hσ.mul_left (1-t)), tsum_mul_left, tsum_mul_left]

end EntropyPhotonNumber

namespace QuantumTrace
open scoped ENNReal

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
end

open QuantumTrace Filter Topology

theorem beamOutput_energy_bound {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    energy (beamOutput η hη ρ σ) ≤ energy ρ + energy σ := by
  have h := beamOutput_energy_le η hη ρ σ
  rw [energyMoment_ofReal (beamOutput_finiteEnergy η hη hρ hσ),
    energyMoment_ofReal hρ, energyMoment_ofReal hσ,
    ← ENNReal.ofReal_add (energy_nonneg ρ) (energy_nonneg σ)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (energy_nonneg ρ) (energy_nonneg σ))).mp h

theorem regularizedOutput_energy_bound {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) {τD τ0 ρ σ : State n}
    (hD : FiniteEnergy τD) (h0 : FiniteEnergy τ0) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    energy (regularizedOutput η δ κ hη hδ hκ τD τ0 ρ σ) ≤
      energy ρ+energy σ+energy τD+energy τ0 := by
  let γ := beamOutput (1-δ) ⟨sub_nonneg.mpr hδ.2, sub_le_self _ hδ.1⟩ (beamOutput η hη ρ σ) τD
  have hg := beamOutput_finiteEnergy (1-δ) ⟨sub_nonneg.mpr hδ.2, sub_le_self _ hδ.1⟩ (beamOutput_finiteEnergy η hη hρ hσ) hD
  have hb := beamOutput_energy_bound (1-δ) ⟨sub_nonneg.mpr hδ.2, sub_le_self _ hδ.1⟩
    (beamOutput_finiteEnergy η hη hρ hσ) hD
  have ha := beamOutput_energy_bound η hη hρ hσ
  change energy (mixture _ _ γ τ0) ≤ _
  apply (mixture_energy (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
    (ρ := γ) (σ := τ0) hg h0).le.trans
  have hp := energy_nonneg γ
  have hq := energy_nonneg τ0
  have hb' : energy γ ≤ energy ρ+energy σ+energy τD := by dsimp [γ]; linarith
  nlinarith [mul_nonneg hκ.1 hp, mul_nonneg (sub_nonneg.mpr hκ.2) hq]

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
open OAI OAI.EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open QuantumTrace Filter Topology


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.regularizedOutput_energy_bound := @_root_.OAI.EntropyPhotonNumber.regularizedOutput_energy_bound
