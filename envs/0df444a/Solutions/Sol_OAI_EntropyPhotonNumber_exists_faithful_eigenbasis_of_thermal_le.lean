-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.exists_faithful_eigenbasis_of_thermal_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:31:02.281339+00:00
-- url     : https://prove2.me/submissions/bfb2025f-08e8-41f5-9363-62b031b431a8

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean:L653-L674
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.exists_faithful_eigenbasis_of_thermal_le. The node keeps its source
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
import Theorems.Thm_OAI_QuantumTrace_exists_positive_eigenbasis

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

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

end

theorem trace_one_numberBasis {n : ℕ} (ρ : State n) :
    HasSum (fun k => (inner ℂ (numberBasis n k) (ρ.op (numberBasis n k))).re) 1 := by
  simpa only [numberBasis_apply, entry] using ρ.trace_one

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

theorem eigenbasis_quadratic_pos (b : HilbertBasis I ℂ E) (T : E →L[ℂ] E)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (he : ∀ i, T (b i) = (p i : ℂ) • b i)
    {x : E} (hx : x ≠ 0) : 0 < (inner ℂ x (T x)).re := by
  classical
  have hex : ∃ i, inner ℂ (b i) x ≠ 0 := by
    by_contra! h
    apply hx
    apply b.repr.injective
    apply lp.ext
    funext i
    rw [map_zero, HilbertBasis.repr_apply_apply]
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hs := hasSum_quadratic_eigenbasis b T p he x
  have hn : ∀ i, 0 ≤ p i*‖inner ℂ (b i) x‖^2 := fun i => mul_nonneg (hp i).le (sq_nonneg _)
  have ht := hs.summable.le_tsum i (fun j _ => hn j)
  rw [hs.tsum_eq] at ht
  exact (mul_pos (hp i) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi))).trans_le ht

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace

theorem exists_faithful_eigenbasis_of_thermal_le {n : ℕ} (ρ : State n)
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op) :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ ∀ j, ρ.op (b j) = (p j : ℂ) • b j := by
  obtain ⟨J, b, p, hp, hs, he⟩ := exists_positive_eigenbasis (numberBasis n) ρ.positive
    (trace_one_numberBasis ρ)
  refine ⟨J, b, p, ?_, hs, he⟩
  intro j
  have ht := eigenbasis_quadratic_pos (numberBasis n) ((κ : ℂ) • (thermalState n r hr).op)
    (fun k => κ*thermalWeight n r k) (fun k => mul_pos hκ (thermalWeight_pos n hr k))
    (fun k => by simp only [smul_apply, thermalState, diagonalState_eigen, smul_smul,
      Complex.ofReal_mul]) (b.orthonormal.ne_zero j)
  have hh := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hle)).re_inner_nonneg_right (b j)
  have hvalue : (inner ℂ (b j) (ρ.op (b j))).re = p j := by
    rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp
  simp only [sub_apply, inner_sub_right] at hh
  change 0 ≤ (inner ℂ (b j) (ρ.op (b j))).re -
    (inner ℂ (b j) (((κ : ℂ) • (thermalState n r hr).op) (b j))).re at hh
  rw [hvalue] at hh
  linarith

end

open QuantumTrace Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
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
open QuantumTrace


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.exists_faithful_eigenbasis_of_thermal_le := @_root_.OAI.EntropyPhotonNumber.exists_faithful_eigenbasis_of_thermal_le
