-- Prove2me | solution 2 for OAI.EntropyPhotonNumber.SpectralLogData.centeredEnergy_lowerEnergy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:39:43.862461+00:00
-- url     : https://prove2.me/submissions/5383661a-abd9-4217-af0f-04b45d835e16

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Minimum.lean:L470-L496
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.SpectralLogData.centeredEnergy_lowerEnergy. The node keeps its source
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

-- ---- from OAI.InformationTheory.PhotonNumber.Minimum ----
-- ---- inlined from OAI.InformationTheory.PhotonNumber.Generator: weakMean_trace and its helper ----
-- (proved here instead of imported, so this solution does not depend on that platform node)
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
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

theorem single_ladder_inner (j : Fin n) (x y : Fock n) :
    inner ℂ (sandwich 0 3 (by omega) j x) (inverseWeight 3 y)=
      inner ℂ (inverseWeight 3 x) (creationSandwich 0 3 (by omega) j y) := by
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) :
      inner ℂ (inverseWeight 3 x k) (creationSandwich 0 3 (by omega) j y k)=0 := by
    have hkj : k j=0 := by
      by_contra hne
      exact hk ⟨down j k,up_down j k (Nat.pos_of_ne_zero hne)⟩
    rw [creationSandwich_zero _ _ _ _ _ _ hkj,inner_zero_right]
  have hh := (up_injective j).hasSum_iff hz |>.mpr
    (lp.hasSum_inner (𝕜:=ℂ) (inverseWeight 3 x) (creationSandwich 0 3 (by omega) j y))
  apply HasSum.unique (lp.hasSum_inner (𝕜:=ℂ) (sandwich 0 3 (by omega) j x) (inverseWeight 3 y))
  convert! hh using 1
  ext k
  simp only [Function.comp_def,RCLike.inner_apply,single_lower_third_apply,
    single_raise_third_apply,up_same,down_up,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
    ↓reduceIte,Nat.cast_add,Nat.cast_one,map_mul,Complex.conj_ofReal]
  ring
end BeamLadder

namespace EntropyPhotonNumber

namespace WeightedColumns
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem weakMean_trace (r : ℝ) (j : Fin n) :
    X.weakMean r j=∑' i, inner ℂ (sandwich 0 3 (by omega) j (X.vector i))
      (inverseWeight 3 (X.vector i)) := by
  have he : CrossEnsemble.pairing (fun i => creationSandwich 0 3 (by omega) j (X.vector i))
      (fun i => inverseWeight 3 (X.vector i)) 1=
    CrossEnsemble.pairing (fun i => inverseWeight 3 (X.vector i))
      (fun i => sandwich 0 3 (by omega) j (X.vector i)) 1 := by
    unfold CrossEnsemble.pairing
    apply tsum_congr
    intro i
    simpa only [one_apply_eq_self] using (single_ladder_inner j (X.vector i) (X.vector i)).symm
  unfold weakMean singleWeak
  rw [he]
  simp only [CrossEnsemble.pairing,one_apply_eq_self]
  ring

end WeightedColumns

end EntropyPhotonNumber

end

end OAI

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

end

open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
variable {n : ℕ}
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

theorem weakMean_hasSum (X : WeightedColumns ρ) (r : ℝ) (j : Fin n) :
    HasSum (fun i => inner ℂ (sandwich 0 3 (by omega) j (X.vector i))
      (inverseWeight 3 (X.vector i))) (X.weakMean r j) := by
  rw [X.weakMean_trace]
  exact (EnsembleL2.inner_sum _ _
    (CrossEnsemble.applied_summable X.summable (sandwich 0 3 (by omega) j))
    X.normalized.summable).summable.hasSum

end EntropyPhotonNumber.WeightedColumns

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem sub_smul_square (x y : E) (μ : ℂ) :
    ‖x-μ • y‖^2=‖x‖^2+‖μ‖^2*‖y‖^2-2*(μ*inner ℂ x y).re := by
  rw [norm_sub_sq (𝕜:=ℂ),norm_smul,mul_pow,inner_smul_right]
  change ‖x‖^2-2*(μ*inner ℂ x y).re+‖μ‖^2*‖y‖^2=_
  ring

theorem centered_square (x y : I → E) (e : ℝ) (μ : ℂ)
    (hx : HasSum (fun i => ‖x i‖^2) e) (hy : HasSum (fun i => ‖y i‖^2) 1)
    (hxy : HasSum (fun i => inner ℂ (x i) (y i)) (conj μ)) :
    HasSum (fun i => ‖x i-μ • y i‖^2) (e-‖μ‖^2) := by
  have hh := (hx.add (hy.mul_left (‖μ‖^2))).sub
    (((hxy.mul_left μ).mapL Complex.reCLM).mul_left 2)
  simpa only [sub_smul_square,Complex.reCLM_apply,Complex.mul_conj,Complex.normSq_eq_norm_sq,
    Complex.ofReal_re,mul_one,show e+‖μ‖^2-2*‖μ‖^2=e-‖μ‖^2 by ring] using hh
end EnsembleL2

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem centeredEnergy_lowerEnergy (t : ℝ) (ht : 0<t) :
    G.centeredEnergy=∑ j, (G.weightedColumns.lowerEnergy j-‖G.annihilationMean j‖^2) := by
  apply Finset.sum_congr rfl
  intro j _
  have he := EnsembleL2.centered_square
    (fun i => sandwich 0 3 (by omega) j (G.spectralColumns i))
    (fun i => inverseWeight 3 (G.spectralColumns i)) (G.weightedColumns.lowerEnergy j)
    (G.annihilationMean j)
    (CrossEnsemble.applied_summable G.spectralColumns_summable (sandwich 0 3 (by omega) j)).hasSum
    G.spectralColumns_normalized
    (by
      have hh := G.weightedColumns.weakMean_hasSum t j
      rw [G.weakMean_eq_conj t ht j] at hh
      exact hh)
  rw [← he.tsum_eq]
  apply tsum_congr
  intro i
  congr 2
  simp only [centeredLadder,Bool.false_eq_true,↓reduceIte,ContinuousLinearMap.comp_apply,
    sub_apply,smul_apply,lowering]
  have hu : inverseWeight 1 (inverseWeight 2 (G.spectralColumns i))=inverseWeight 3 (G.spectralColumns i) := by
    change (inverseWeight 1 ∘L inverseWeight 2) (G.spectralColumns i)=_
    rw [← inverseWeight_add]
  rw [hu]
  congr 1
  exact congrArg (fun A : Fock n →L[ℂ] Fock n => A (G.spectralColumns i))
    (sandwich_right_inverse 0 1 2 (by omega) j).symm
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

end EntropyPhotonNumber.Regularization

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric

namespace ThermalSetup
variable (P : ThermalSetup)
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
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.SpectralLogData
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Metric
open MeasureTheory Set Filter Topology Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology MeasureTheory
open QuantumTrace Annihilation WeightedGenerator ThermalMetric


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.SpectralLogData.centeredEnergy_lowerEnergy := @_root_.OAI.EntropyPhotonNumber.SpectralLogData.centeredEnergy_lowerEnergy
