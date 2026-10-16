-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.ThermalSetup.physical_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:50:10.60265+00:00
-- url     : https://prove2.me/submissions/49788c56-b54b-4d40-ad1b-e371b57101cb

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Minimum.lean:L1312-L1371
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.ThermalSetup.physical_estimate. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum
import Theorems.Thm_OAI_EntropyPhotonNumber_beamOutput_powerMoment_le
import Theorems.Thm_OAI_EntropyPhotonNumber_physical_defect_mode_bound
import Theorems.Thm_OAI_EntropyPhotonNumber_replaced_threeport_weak
import Theorems.Thm_OAI_KrausBounded_dual_one
import Theorems.Thm_OAI_ThermalDual_aggregate_bound
import Theorems.Thm_OAI_ThermalDual_defect_young
import Theorems.Thm_OAI_ThermalMetric_defectVector_mem_centeredSpace
import Theorems.Thm_OAI_WeightedGenerator_weakDefect_spectral

-- ---- from OAI.InformationTheory.PhotonNumber.ThermalMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric

section
open EntropyPhotonNumber DiagonalForms.System

end

section
open DiagonalForms.System

end

section
open EntropyPhotonNumber
variable {J : Type*}

theorem defectVector_pairing (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (z : J × J → ℂ)
    (hz : Summable (fun a : J × J => metricCoefficient r (p a.1) (p a.2)*‖z a‖^2)) :
    HasSum (fun a : J × J => (defectCoefficient r (p a.1) (p a.2):ℂ)*conj (d a)*z a)
      (inner ℂ (defectVector r hr p hp d hd)
        (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
          (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))) := by
  have hh := lp.hasSum_inner (𝕜 := ℂ) (defectVector r hr p hp d hd)
    (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
      (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))
  convert! hh using 1
  ext a
  simp only [defectVector_apply, weightedVector_apply, RCLike.inner_apply,
    map_mul, Complex.ofReal_div, map_div₀, Complex.conj_ofReal]
  have hn : (Real.sqrt (metricCoefficient r (p a.1) (p a.2)):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (metricCoefficient_pos hr (hp a.1) (hp a.2))).ne'
  field_simp

end

section
variable {J : Type*}

end

open scoped ComplexConjugate
variable {J : Type*}

theorem diagonal_mean_summable (p : J → ℝ) (hp : ∀ j, 0≤p j) (hs : Summable p)
    (d : J × J → ℂ) (hd : Summable (fun a : J × J => p a.2*‖d a‖^2)) :
    Summable (fun j => (p j:ℂ)*d (j,j)) := by
  have hi : Function.Injective (fun j : J => (j,j)) := fun _ _ he => (Prod.mk.inj he).1
  have hh := hd.comp_injective hi
  apply Summable.of_norm_bounded (hh.add hs)
  intro j
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
  have hn : ‖d (j,j)‖≤‖d (j,j)‖^2+1 := by nlinarith [sq_nonneg (‖d (j,j)‖-1)]
  simpa only [mul_add, mul_one, Function.comp_apply] using mul_le_mul_of_nonneg_left hn (hp j)

theorem diagonal_centering (p : J → ℝ) (hs : HasSum p 1)
    (d : J × J → ℂ) (hd : Summable (fun j => (p j:ℂ)*d (j,j))) :
    HasSum (fun j => (p j:ℂ)*(d (j,j)-diagonalMean p d)) 0 := by
  have hh := hd.hasSum.sub ((Complex.hasSum_ofReal.mpr hs).mul_right (diagonalMean p d))
  simpa only [diagonalMean, Complex.ofReal_one, one_mul, sub_self, mul_sub] using hh

end ThermalMetric

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ} {J : Type*}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace ThermalMetric
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ}

theorem lowering_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    lowering j (inverseWeight 2 x) k=
      (Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  rw [lowering_apply]
  change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
  rw [← inverseWeight_add]

theorem raising_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    raising j (inverseWeight 2 x) k=
      (Real.sqrt (k j:ℝ):ℂ)*inverseWeight 3 x (down j k) := by
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · simp only [raising_zero j _ k hk, hk, Nat.cast_zero, Real.sqrt_zero,
      Complex.ofReal_zero, zero_mul]
  · rw [raising_up]
    change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
    rw [← inverseWeight_add, up_same, down_up]
    norm_cast
end Annihilation

namespace EntropyPhotonNumber
open Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open Annihilation WeightedGenerator
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.BeamForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

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

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem single_lower_third_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    sandwich 0 3 (by omega) j x k=
      (Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  simp only [sandwich_apply,coefficient,inverseWeight_apply,pow_zero,one_mul]
  push_cast
  ring

theorem single_raise_third_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    creationSandwich 0 3 (by omega) j x k=
      (if k j=0 then (0:ℂ) else (Real.sqrt (k j:ℝ):ℂ))*inverseWeight 3 x (down j k) := by
  by_cases hk : k j=0
  · rw [creationSandwich_zero _ _ _ _ _ k hk,ite_eq_left hk,zero_mul]
  · rw [ite_eq_right hk]
    obtain ⟨a,rfl⟩ : ∃ a,k=up j a := ⟨down j k,(up_down j k (Nat.pos_of_ne_zero hk)).symm⟩
    rw [creationSandwich_up,down_up,up_same]
    simp only [creationCoefficient,inverseWeight_apply,pow_zero,one_mul]
    push_cast
    ring

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end BeamLadder

namespace EnsemblePullback

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I : Type*}

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I J : Type*}

end EnsemblePullback

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {I : Type*}
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I : Type*}

end BeamLadder

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I K : Type*}

end WeightedGenerator

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I : Type*}

end CrossEnsemble

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Generator ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

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

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I : Type*}

end PhysicalGenerator

namespace QuantumTrace
end QuantumTrace

namespace PhysicalGenerator

section
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ} {I : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder

namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end KrausBounded

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}
theorem conjugate_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    conjugate (n:=n) η hη 1=1 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [conjugate,liftLeft_one,ContinuousLinearMap.comp_apply,one_apply_eq_self]
  change (beamUnitary η hη).symm (beamUnitary η hη x)=x
  exact (beamUnitary η hη).symm_apply_apply x
end BeamLadder

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem expectation_one : X.expectation 1=1 := by
  have hh := X.normalized.mapL Complex.ofRealCLM
  unfold expectation CrossEnsemble.pairing
  have hs : HasSum (fun i => inner ℂ (inverseWeight 3 (X.vector i))
      ((1 : Fock n →L[ℂ] Fock n) (inverseWeight 3 (X.vector i)))) (1:ℂ) := by
    convert! hh using 1
    ext i
    simp only [one_apply_eq_self,inner_self_eq_norm_sq_to_K,Complex.ofRealCLM_apply,Complex.ofReal_pow]
    rfl
  exact hs.tsum_eq

theorem rawSlice_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) : X.rawSlice η hη 1=1 := by
  simp only [rawSlice,conjugate_one,conditionalLeft,KrausBounded.dual_one]

theorem rawSliceRight_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) : X.rawSliceRight η hη 1=1 := by
  simp only [rawSliceRight,conjugate_one,conditionalRight,KrausBounded.dual_one]

end WeightedColumns

end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end BeamLadder

namespace EntropyPhotonNumber

namespace WeightedColumns
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.SpectralLog ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

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

namespace SquareAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

variable [CompleteSpace E]

end SquareAnalysis

namespace QuantumTrace
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace Annihilation

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n}

end GibbsData
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end SpectralLogData
end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem annihilation_mean_summable (j : Fin n) :
    Summable (fun r => (G.probability r:ℂ)*G.annihilationMatrix j (r,r)) := by
  apply diagonal_mean_summable G.probability (fun r => (G.probability_pos r).le)
    G.probability_sum.summable
  have hh := nonlog_summable G.basis G.spectralColumns G.spectralColumns_summable j false
  simpa only [spectralGain_lowering_sq G.basis G.probability G.probability_pos,
    annihilationMatrix] using hh

theorem centeredMatrix_mean_zero (j : Fin n) :
    HasSum (fun r => (G.probability r:ℂ)*G.centeredMatrix j (r,r)) 0 := by
  classical
  simpa only [centeredMatrix, centeredEntry, ↓reduceIte, annihilationMean, annihilationMatrix]
    using diagonal_centering G.probability G.probability_sum
      (G.annihilationMatrix j) (G.annihilation_mean_summable j)

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

end

end EntropyPhotonNumber

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace

end

open QuantumTrace Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.GibbsVariational ----
namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal

namespace QuantumTrace

section
open scoped BigOperators
open Filter Topology

namespace StochasticOverlap
variable {I J : Type*} (a : StochasticOverlap I J)

end StochasticOverlap
end

section
open scoped BigOperators
variable {I J : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {J : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace
variable {n : ℕ} {J : Type*} [Nonempty J]

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
end

section
open QuantumTrace TraceEnsemble

end

section
open QuantumTrace

end

section
open QuantumTrace TensorLp

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end

section
open QuantumTrace
namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end

open QuantumTrace TraceEnsemble

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData

end EntropyPhotonNumber

namespace TensorLp
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

theorem powerMoment_eq {n : ℕ} (m : ℕ) (ρ : State n) :
    powerMoment m ρ = ∑' k, ENNReal.ofReal ((1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re) := by
  unfold powerMoment matrixMoment
  congr 1
  funext k
  rw [ENNReal.ofReal_mul (pow_nonneg (by positivity) _),
    ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  rfl

theorem finiteMoment_iff {n : ℕ} (m : ℕ) (ρ : State n) :
    FiniteMoment m ρ ↔ powerMoment m ρ < ⊤ := by
  rw [powerMoment_eq]
  have hp (k : NumberIndex n) : 0 ≤ (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re :=
    mul_nonneg (pow_nonneg (by positivity) _) (ρ.positive.re_inner_nonneg_right _)
  constructor
  · intro h
    exact h.tsum_ofReal_lt_top
  · intro h
    have hs := ENNReal.summable_toReal h.ne
    change Summable (fun k => (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re)
    simpa only [ENNReal.toReal_ofReal (hp _)] using hs

theorem beamOutput_finiteMoment {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) {m : ℕ} {ρA ρB : State n}
    (hA : FiniteMoment m ρA) (hB : FiniteMoment m ρB) : FiniteMoment m (beamOutput η hη ρA ρB) := by
  apply (finiteMoment_iff _ _).mpr
  exact (beamOutput_powerMoment_le η hη m ρA ρB).trans_lt
    (ENNReal.mul_lt_top ((finiteMoment_iff _ _).mp hA) ((finiteMoment_iff _ _).mp hB))

end EntropyPhotonNumber

end

end OAI

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

omit [CompleteSpace E] in
theorem pairing_sub_right (u v w : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2))
    (c : ℂ) (Z : E →L[ℂ] E) :
    pairing u (fun i => v i-c • w i) Z=pairing u v Z-conj c*pairing u w Z := by
  simp only [pairing, inner_sub_left, inner_smul_left]
  rw [(pairing_summable hu hv Z).tsum_sub ((pairing_summable hu hw Z).mul_left (conj c)), tsum_mul_left]

omit [CompleteSpace E] in
theorem pairing_sub_left (u v w : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2))
    (c : ℂ) (Z : E →L[ℂ] E) :
    pairing (fun i => u i-c • v i) w Z=pairing u w Z-c*pairing v w Z := by
  simp only [pairing, map_sub, map_smul, inner_sub_right, inner_smul_right]
  rw [(pairing_summable hu hw Z).tsum_sub ((pairing_summable hv hw Z).mul_left c), tsum_mul_left]
end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation BeamLadder ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem centeredLadder_lower (j : Fin n) (μ : ℂ) (x : Fock n) :
    centeredLadder j μ false x=sandwich 0 3 (by omega) j x-μ • inverseWeight 3 x := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simp only [centeredLadder, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, hw]
  congr 1
  ext k
  rw [lowering_weighted_apply, single_lower_third_apply]

theorem centeredLadder_raise (j : Fin n) (μ : ℂ) (x : Fock n) :
    centeredLadder j μ true x=creationSandwich 0 3 (by omega) j x-conj μ • inverseWeight 3 x := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simp only [centeredLadder, ↓reduceIte, ContinuousLinearMap.comp_apply, sub_apply, smul_apply, hw]
  congr 1
  ext k
  rw [raising_weighted_apply, single_raise_third_apply]
  by_cases hk : k j=0
  · simp only [hk, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul, ↓reduceIte]
  · rw [ite_eq_right hk]

theorem weakDefect_uncentered (t : ℝ) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2)) (j : Fin n) (μ : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    weakDefect t x j μ Z=singleWeak t j x Z-conj μ*
      CrossEnsemble.pairing (fun r => inverseWeight 3 (x r)) (fun r => inverseWeight 3 (x r)) Z := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  simp only [weakDefect, centeredLadder_lower, centeredLadder_raise]
  rw [CrossEnsemble.pairing_sub_right _ _ _ hi hl hi,
    CrossEnsemble.pairing_sub_left _ _ _ hr hi hi]
  unfold singleWeak
  ring
end WeightedGenerator

namespace ThermalSpectral.Space
open EntropyPhotonNumber Annihilation WeightedGenerator ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} (S : Space (Fock n))

theorem defectFunctional_observable (x : S.I → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (S.p r):ℂ) • S.basis r)
    (j : Fin n) (μ : ℂ)
    (hd : Summable (fun a : S.I × S.I =>
      (1-frequency S.r (S.p a.1) (S.p a.2))*defectCoefficient S.r (S.p a.1) (S.p a.2)*
        ‖centeredEntry S.basis S.p x j μ a.1 a.2‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    defectFunctional S.r S.rpos S.p S.pos (fun a => centeredEntry S.basis S.p x j μ a.1 a.2) hd
        (S.observable Z)=weakDefect S.r x j μ Z := by
  exact (defectVector_pairing S.r S.rpos S.p S.pos _ hd
    (fun a => inner ℂ (S.basis a.1) (Z (S.basis a.2)))
    (observable_summable S.basis S.p S.pos S.sum.summable S.r S.rpos Z)).unique
      (weakDefect_spectral S.basis S.p S.pos x hx hi S.r j μ Z)

theorem defectFunctional_one (d : S.I × S.I → ℂ) (hd)
    (hc : HasSum (fun j => (S.p j:ℂ)*d (j,j)) 0) :
    defectFunctional S.r S.rpos S.p S.pos d hd (S.observable 1)=0 := by
  have hh := defectVector_mem_centeredSpace S.r S.rpos S.p S.pos S.sum.summable d hd hc
  change inner ℂ (identityVector S.r S.rpos S.p S.pos S.sum.summable)
    (defectVector S.r S.rpos S.p S.pos d hd)=0 at hh
  change inner ℂ (defectVector S.r S.rpos S.p S.pos d hd) (S.observable 1)=0
  have he : S.observable 1=identityVector S.r S.rpos S.p S.pos S.sum.summable :=
    observableMap_id S.basis S.p S.pos S.sum.summable S.r S.rpos
  rw [he, ← inner_conj_symm, hh, map_zero]

end ThermalSpectral.Space

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

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

namespace EnsembleL2

section
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace BKM
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace TensorLp
open KrausBounded
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

end EntropyPhotonNumber

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

end EntropyPhotonNumber

namespace EnsembleL2
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end

section
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end CenteredTests

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

end EntropyPhotonNumber

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space ThermalMetric
variable {n : ℕ}

end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem ambientDefect_observable (t : ℝ) (ht : 0<t) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    G.ambientDefect t ht j ((G.thermalSpace t ht).observable Z)=
      weakDefect t G.spectralColumns j (G.annihilationMean j) Z :=
  (G.thermalSpace t ht).defectFunctional_observable G.spectralColumns G.spectralColumns_summable
    G.spectralColumns_inverse j (G.annihilationMean j) (G.centeredMatrix_defect_summable t j) Z

theorem ambientDefect_one (t : ℝ) (ht : 0<t) (j : Fin n) :
    G.ambientDefect t ht j ((G.thermalSpace t ht).observable 1)=0 :=
  (G.thermalSpace t ht).defectFunctional_one (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable t j) (G.centeredMatrix_mean_zero j)

theorem weakMean_eq_conj (t : ℝ) (ht : 0<t) (j : Fin n) :
    G.weightedColumns.weakMean t j=conj (G.annihilationMean j) := by
  have hz := G.ambientDefect_one t ht j
  rw [G.ambientDefect_observable, weakDefect_uncentered _ _ G.spectralColumns_summable] at hz
  change G.weightedColumns.weakMean t j-conj (G.annihilationMean j)*G.weightedColumns.expectation 1=0 at hz
  rw [G.weightedColumns.expectation_one, mul_one] at hz
  exact sub_eq_zero.mp hz

end EntropyPhotonNumber.SpectralLogData

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Duality ----
namespace OAI

noncomputable section

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end EntropyPhotonNumber.SpectralLogData

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace TensorLp
open EntropyPhotonNumber
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded BeamLadder Annihilation
variable {n : ℕ}

namespace WeightedColumns
variable {ρ σ τ : State n}

end WeightedColumns
end EntropyPhotonNumber

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

end

open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

variable {I J : Type*} [Fintype I] [Fintype J]

end ThermalDual

namespace ThermalSpectral
open EntropyPhotonNumber ThermalMetric
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

section
open EntropyPhotonNumber ThermalMetric ThermalSpectral
open scoped BigOperators
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype K]

end

section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem two_sqrt_norm_sq (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (x y : ℂ) :
    ‖(Real.sqrt a:ℂ)*x+(Real.sqrt b:ℂ)*y‖^2 ≤ 2*(a*‖x‖^2+b*‖y‖^2) := by
  have hn := pow_le_pow_left₀ (norm_nonneg ((Real.sqrt a:ℂ)*x+(Real.sqrt b:ℂ)*y))
    (norm_add_le ((Real.sqrt a:ℂ)*x) ((Real.sqrt b:ℂ)*y)) 2
  have hp := sq_nonneg (‖(Real.sqrt a:ℂ)*x‖-‖(Real.sqrt b:ℂ)*y‖)
  have he (r : ℝ) (hr : 0≤r) (z : ℂ) : ‖(Real.sqrt r:ℂ)*z‖^2=r*‖z‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr]
  nlinarith [he a ha x, he b hb y]

end

open scoped ComplexConjugate

end ThermalDual

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Minimum ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology _root_.Complex _root_.OAI.Complex Metric
open MeasureTheory Set Filter Topology _root_.Complex _root_.OAI.Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology _root_.Complex _root_.OAI.Complex MeasureTheory

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ}

theorem twoPortLambda_pos {η θ : ℝ} (hη : η ∈ Set.Ioo 0 1) (hθ : 0<θ) (i : Fin 2) :
    0<twoPortLambda η θ i := by
  fin_cases i
  · exact mul_pos hθ hη.1
  · exact mul_pos hθ (sub_pos.mpr hη.2)

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp BeamLadder
open scoped ComplexConjugate
variable {n : ℕ}

theorem physical_mean_covariance (η θ d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i))
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (j : Fin n) :
    V.weakMean (outputReference η θ a d) j=
      (Real.sqrt (twoPortLambda η θ 0):ℂ)*conj ((G 0).annihilationMean j)+
      (Real.sqrt (twoPortLambda η θ 1):ℂ)*conj ((G 1).annihilationMean j) := by
  change 0<η ∧ η<1 at hη
  change 0<θ ∧ θ<1 at hθ
  have hh := replaced_threeport_weak η θ 0 (a 0) (a 1) d
    ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩
    (ρ 0) (ρ 1) τD m γ ω γ h1 h2 (G 0).weightedColumns (G 1).weightedColumns
    D M V O V hd hr0 hD hO (by
      simp only [sub_zero,Complex.ofReal_one,Complex.ofReal_zero,one_smul]
      apply ContinuousLinearMap.ext
      intro vector
      simp only [add_apply,smul_apply,zero_smul,add_zero]) j 1
  have hm : V.weakMean (outputReference η θ a d) j=
      (Real.sqrt θ:ℂ)*(Real.sqrt η:ℂ)*(G 0).weightedColumns.weakMean (a 0) j+
      (Real.sqrt θ:ℂ)*(Real.sqrt (1-η):ℂ)*(G 1).weightedColumns.weakMean (a 1) j := by
    have ho : D.rawSlice θ (show θ ∈ Set.Icc 0 1 from ⟨hθ.1.le,hθ.2.le⟩) 1=1 := D.rawSlice_one _ _
    have hi : (G 1).weightedColumns.rawSlice η (show η ∈ Set.Icc 0 1 from ⟨hη.1.le,hη.2.le⟩) 1=1 :=
      (G 1).weightedColumns.rawSlice_one _ _
    have hj : (G 0).weightedColumns.rawSliceRight η (show η ∈ Set.Icc 0 1 from ⟨hη.1.le,hη.2.le⟩) 1=1 :=
      (G 0).weightedColumns.rawSliceRight_one _ _
    simp only [ho,hi,hj,sub_zero,Complex.ofReal_one,one_mul] at hh
    exact hh
  rw [hm, (G 0).weakMean_eq_conj (a 0) (ha 0), (G 1).weakMean_eq_conj (a 1) (ha 1)]
  simp only [twoPortLambda, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.sqrt_mul hθ.1.le, Complex.ofReal_mul]

 theorem physical_mean_bound (η θ κ d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ≤1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i))
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (j : Fin n) :
    (1-κ)*‖V.weakMean (outputReference η θ a d) j‖^2≤
      2*∑ i, ((1-κ)*twoPortLambda η θ i)*‖(G i).annihilationMean j‖^2 := by
  rw [physical_mean_covariance η θ d a hη hθ hd ha hr0 ρ τD m γ ω h1 h2 G D M V O hD hO j]
  have hh := mul_le_mul_of_nonneg_left
    (ThermalDual.two_sqrt_norm_sq _ _ (twoPortLambda_pos hη hθ.1 0).le (twoPortLambda_pos hη hθ.1 1).le
      (conj ((G 0).annihilationMean j)) (conj ((G 1).annihilationMean j))) (sub_nonneg.mpr hκ)
  simp only [Complex.norm_conj] at hh
  simp only [Fin.sum_univ_two]
  convert! hh using 1; ring
end

open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
variable {n : ℕ}
theorem physical_defect_triangle (η θ κ ε d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ ∈ Set.Icc 0 1) (hκ1 : κ<1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i)) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (hh₁ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 0).basis (G 0).probability
        (BKM.center (G 0).basis (G 0).probability
          (rawFirstSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 1) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 0*(h (outputReference η θ a d)/h (a 0))*
        BKM.quadratic G0.basis G0.probability Z)
    (hh₂ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 1).basis (G 1).probability
        (BKM.center (G 1).basis (G 1).probability
          (rawSecondSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 1*(h (outputReference η θ a d)/h (a 1))*
        BKM.quadratic G0.basis G0.probability Z)
    (hr : (1+ε)*(∑ i, twoPortLambda η θ i*a i) ≤ outputReference η θ a d)
    (hs : (1+ε)*(∑ i, twoPortLambda η θ i*(a i+1)) ≤ outputReference η θ a d+1)
 :
    Real.sqrt (∑ j, ‖G0.defect (outputReference η θ a d) hr0 j‖^2) ≤ Real.sqrt (∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).defect (a i) (ha i) j‖^2))+
      Real.sqrt (2*κ)*mixtureConstant (outputReference η θ a d)*Real.sqrt (∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).annihilationMean j‖^2)) := by
  exact ThermalDual.aggregate_bound (fun i => (1-κ)*twoPortLambda η θ i)
    (fun i => mul_nonneg (sub_nonneg.mpr hκ.2) (twoPortLambda_pos hη hθ.1 i).le)
    (fun j => ‖G0.defect (outputReference η θ a d) hr0 j‖)
    (fun j => ‖V.weakMean (outputReference η θ a d) j‖)
    (fun i j => ‖(G i).defect (a i) (ha i) j‖) (fun i j => ‖(G i).annihilationMean j‖)
    (fun j => norm_nonneg (G0.defect (outputReference η θ a d) hr0 j)) (fun j => norm_nonneg (V.weakMean (outputReference η θ a d) j)) (mixtureConstant (outputReference η θ a d)) κ
    (mixtureConstant_pos hr0).le hκ
    (physical_mean_bound η θ κ d a hη hθ hκ.2 hd ha hr0 ρ τD m γ ω h1 h2 G D M V O hD hO)
    (physical_defect_mode_bound η θ κ ε d a hη hθ hκ hκ1 hd ha hr0 ρ τD m γ ω ρ0 h1 h2 G G0 D M V O hD hO hrepl hh₁ hh₂ hr hs)

theorem physical_defect_estimate (η θ κ ε d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ ∈ Set.Icc 0 1) (hκ1 : κ<1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i)) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (hh₁ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 0).basis (G 0).probability
        (BKM.center (G 0).basis (G 0).probability
          (rawFirstSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 1) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 0*(h (outputReference η θ a d)/h (a 0))*
        BKM.quadratic G0.basis G0.probability Z)
    (hh₂ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 1).basis (G 1).probability
        (BKM.center (G 1).basis (G 1).probability
          (rawSecondSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 1*(h (outputReference η θ a d)/h (a 1))*
        BKM.quadratic G0.basis G0.probability Z)
    (hr : (1+ε)*(∑ i, twoPortLambda η θ i*a i) ≤ outputReference η θ a d)
    (hs : (1+ε)*(∑ i, twoPortLambda η θ i*(a i+1)) ≤ outputReference η θ a d+1)
    (hε : 0<ε)
    (hk : κ≤ε^2/(4*(ε+2)*mixtureConstant (outputReference η θ a d)^2)) :
    (∑ j, ‖G0.defect (outputReference η θ a d) hr0 j‖^2) ≤ (∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).defect (a i) (ha i) j‖^2))+ε/2*((∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).defect (a i) (ha i) j‖^2))+(∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).annihilationMean j‖^2))) := by
  have hq0 : 0≤∑ j, ‖G0.defect (outputReference η θ a d) hr0 j‖^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hA : 0≤∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).defect (a i) (ha i) j‖^2) := Finset.sum_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hκ.2) (twoPortLambda_pos hη hθ.1 i).le)
    (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  have hM : 0≤∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).annihilationMean j‖^2) := Finset.sum_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hκ.2) (twoPortLambda_pos hη hθ.1 i).le)
    (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  have hh := ThermalDual.defect_young (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (mixtureConstant_pos hr0) hκ.1 hε hk (physical_defect_triangle η θ κ ε d a hη hθ hκ hκ1 hd ha hr0 ρ τD m γ ω ρ0 h1 h2 G G0 D M V O hD hO hrepl hh₁ hh₂ hr hs)
  simpa only [Real.sq_sqrt hq0, Real.sq_sqrt hA, Real.sq_sqrt hM] using hh
end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace TensorLp
variable {A B I J : Type*}
end TensorLp

namespace EntropyPhotonNumber.WeightedColumns
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {ρ σ τ : State n}

end EntropyPhotonNumber.WeightedColumns

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
end Annihilation

namespace EntropyPhotonNumber.WeightedColumns

section
open QuantumTrace Annihilation
variable {n : ℕ} {ρ : State n}

end

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

section
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ σ τ : State n}

end

open QuantumTrace
variable {n : ℕ}

end EntropyPhotonNumber.WeightedColumns

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace WeightedColumns
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber
open QuantumTrace WeightedColumns
variable {n : ℕ}

end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators ComplexConjugate

section
open TensorLp KrausBounded BeamLadder
variable {n : ℕ}

namespace Regularization
open QuantumTrace
variable (R : Regularization n)

end Regularization
end

open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

namespace GibbsData
variable {k : ℝ} (G : GibbsData n k ρ)
end GibbsData

end EntropyPhotonNumber

section
open scoped BigOperators

namespace WeightedGenerator

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
end

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber.Regularization
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

theorem thermal_state_diagonal (r : ℝ) (hr : 0<r) (k l : NumberIndex n) :
    entry (thermalState n r hr).op k l=if k=l then (thermalWeight n r k:ℂ) else 0 := by
  rw [entry,← numberBasis_apply n k,← numberBasis_apply n l]
  change inner ℂ (numberBasis n k) ((diagonalState _ _ _).op (numberBasis n l))=_
  rw [diagonalState_eigen,inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal k l]
  split_ifs with h
  · subst l; simp only [mul_one]
  · simp only [mul_zero]

end EntropyPhotonNumber.Regularization

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric

namespace ThermalSetup
variable (P : ThermalSetup)
theorem raw_finiteMoment {n m : ℕ} {ρ σ : State n} (hρ : FiniteMoment m ρ) (hσ : FiniteMoment m σ) :
    FiniteMoment m (P.raw ρ σ) :=
  beamOutput_finiteMoment _ _ (beamOutput_finiteMoment _ _ hρ hσ) (thermalState_finiteMoment n m P.d P.hd)
theorem output_op {n : ℕ} (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n) :
    ((P.reg n ζ hζ).output ρ σ).op=((1-P.κ:ℝ):ℂ) • (P.raw ρ σ).op+
      (P.κ:ℂ) • (thermalState n P.r0 P.r0_pos).op := by
  simp only [Regularization.output,reg,regularizedOutput,sub_sub_cancel,mixture,raw,middle]
end ThermalSetup

namespace WeightedColumns
variable {n : ℕ} {ρ : State n}
end WeightedColumns
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end SpectralLogData
end

open QuantumTrace ThermalMetric Annihilation
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end SpectralLogData
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

theorem physical_estimate (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n)
    (G1 : SpectralLogData n ρ) (G2 : SpectralLogData n σ)
    (G0 : SpectralLogData n ((P.reg n ζ hζ).output ρ σ))
    (h6ρ : FiniteMoment 6 ρ) (h6σ : FiniteMoment 6 σ)
    (hh1 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic G1.basis G1.probability
        (BKM.center G1.basis G1.probability (rawFirstSlice P.η P.θ P.η_mem P.θ_mem σ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w1/h P.r1)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z)
    (hh2 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic G2.basis G2.probability
        (BKM.center G2.basis G2.probability (rawSecondSlice P.η P.θ P.η_mem P.θ_mem ρ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w2/h P.r2)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z) :
    G0.defectSquared P.r0 P.r0_pos≤
      P.w1*G1.defectSquared P.r1 P.hr1+P.w2*G2.defectSquared P.r2 P.hr2+
      P.ε/2*(P.w1*G1.defectSquared P.r1 P.hr1+P.w2*G2.defectSquared P.r2 P.hr2+
        (P.w1*G1.meanSquared+P.w2*G2.meanSquared)) := by
  let a : Fin 2 → ℝ := ![P.r1,P.r2]
  have ha : ∀ i, 0<a i := by intro i; fin_cases i; exact P.hr1; exact P.hr2
  let states : Fin 2 → State n := ![ρ,σ]
  let G : (i : Fin 2) → SpectralLogData n (states i) := Fin.cases G1 (Fin.cases G2 (fun i => Fin.elim0 i))
  have hr0 : 0<outputReference P.η P.θ a P.d := P.r0_pos
  let D := WeightedColumns.canonical (thermalState n P.d P.hd) (thermalState_finiteMoment n 6 P.d P.hd)
  let M := WeightedColumns.canonical (P.middle ρ σ) (beamOutput_finiteMoment _ _ h6ρ h6σ)
  let V := WeightedColumns.canonical (P.raw ρ σ) (P.raw_finiteMoment h6ρ h6σ)
  let O := WeightedColumns.canonical (thermalState n P.r0 P.r0_pos) (thermalState_finiteMoment n 6 P.r0 P.r0_pos)
  have hh := physical_defect_estimate P.η P.θ P.κ P.ε P.d a P.hη P.hθ P.κ_mem P.hκ.2 P.hd ha hr0
    states (thermalState n P.d P.hd) (P.middle ρ σ) (P.raw ρ σ) (thermalState n P.r0 P.r0_pos)
    ((P.reg n ζ hζ).output ρ σ) (beamOutput_spec _ _ _ _) (beamOutput_spec _ _ _ _) G G0 D M V O
    (Regularization.thermal_state_diagonal P.d P.hd)
    (Regularization.thermal_state_diagonal P.r0 P.r0_pos) (P.output_op ζ hζ ρ σ) ?_ ?_ ?_ ?_ P.hε P.small_κ
  · simp only [Fin.sum_univ_two] at hh
    change G0.defectSquared P.r0 P.r0_pos≤
      ((1-P.κ)*(P.θ*P.η))*G1.defectSquared P.r1 P.hr1+
      ((1-P.κ)*(P.θ*(1-P.η)))*G2.defectSquared P.r2 P.hr2+
      P.ε/2*(((1-P.κ)*(P.θ*P.η))*G1.defectSquared P.r1 P.hr1+
        ((1-P.κ)*(P.θ*(1-P.η)))*G2.defectSquared P.r2 P.hr2+
        (((1-P.κ)*(P.θ*P.η))*G1.meanSquared+((1-P.κ)*(P.θ*(1-P.η)))*G2.meanSquared)) at hh
    simpa only [w1,w2,mul_assoc] using hh
  · intro Z hZ
    change (1-P.κ)^2*BKM.quadratic G1.basis G1.probability
        (BKM.center G1.basis G1.probability (rawFirstSlice P.η P.θ P.η_mem P.θ_mem σ (thermalState n P.d P.hd) Z))≤
      (1+P.ε)*(1-P.κ)*(P.θ*P.η)*(h P.r0/h P.r1)*BKM.quadratic G0.basis G0.probability Z
    have hc : (1+P.ε)*(1-P.κ)*(P.θ*P.η)*(h P.r0/h P.r1)=((1+P.ε)*P.w1/h P.r1)/(1/h P.r0) := by
      unfold w1
      field_simp [(h_pos P.r0_pos).ne']
    rw [hc]
    exact hh1 Z hZ
  · intro Z hZ
    change (1-P.κ)^2*BKM.quadratic G2.basis G2.probability
        (BKM.center G2.basis G2.probability (rawSecondSlice P.η P.θ P.η_mem P.θ_mem ρ (thermalState n P.d P.hd) Z))≤
      (1+P.ε)*(1-P.κ)*(P.θ*(1-P.η))*(h P.r0/h P.r2)*BKM.quadratic G0.basis G0.probability Z
    have hc : (1+P.ε)*(1-P.κ)*(P.θ*(1-P.η))*(h P.r0/h P.r2)=((1+P.ε)*P.w2/h P.r2)/(1/h P.r0) := by
      unfold w2
      field_simp [(h_pos P.r0_pos).ne']
    rw [hc]
    exact hh2 Z hZ
  · simpa only [Fin.sum_univ_two,twoPortLambda,a,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.head_cons,Matrix.cons_val_fin_one,outputReference] using P.slack_r
  · simpa only [Fin.sum_univ_two,twoPortLambda,a,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.head_cons,Matrix.cons_val_fin_one,outputReference] using P.slack_s

end ThermalSetup

namespace ThermalDual

end ThermalDual
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

end ThermalSetup
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.ThermalSetup
open scoped BigOperators ComplexConjugate
open QuantumTrace ThermalMetric Annihilation


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.ThermalSetup.physical_estimate := @_root_.OAI.EntropyPhotonNumber.ThermalSetup.physical_estimate
