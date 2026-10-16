-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.negativeLog_extended_le_thermal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:48:49.964385+00:00
-- url     : https://prove2.me/submissions/39caf396-be9b-45f7-8af4-71f54e2169f5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L1623-L1641
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.negativeLog_extended_le_thermal. The node keeps its source
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
import Theorems.Thm_OAI_EntropyPhotonNumber_negativeLog_le_thermal

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

theorem basisMoment_ofReal (b : HilbertBasis I ℂ E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : E) (hs : Summable (fun i => w i*‖inner ℂ (b i) x‖^2)) :
    basisMoment b (fun i => ENNReal.ofReal (w i)) x =
      ENNReal.ofReal (∑' i, w i*‖inner ℂ (b i) x‖^2) := by
  simp only [basisMoment, ← ENNReal.ofReal_mul (hw _)]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hw i) (sq_nonneg _)) hs).symm

variable [CompleteSpace E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

theorem numberVectorMoment_eq {n : ℕ} (x : Fock n) :
    numberVectorMoment x = ∑' k, ENNReal.ofReal ((totalNumber k : ℝ)*‖inner ℂ (numberBasis n k) x‖^2) := by
  simp only [numberVectorMoment, basisMoment, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

theorem finiteVectorEnergy_iff {n : ℕ} (x : Fock n) :
    FiniteVectorEnergy x ↔ numberVectorMoment x < ⊤ := by
  rw [numberVectorMoment_eq]
  constructor
  · intro hx
    exact hx.tsum_ofReal_lt_top
  · intro hx
    have hs := ENNReal.summable_toReal hx.ne
    simpa only [FiniteVectorEnergy, ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))] using hs

theorem numberVectorMoment_ofReal {n : ℕ} (x : Fock n) (hx : FiniteVectorEnergy x) :
    numberVectorMoment x = ENNReal.ofReal (vectorEnergy x) := by
  rw [numberVectorMoment_eq]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hx).symm

theorem thermal_log_constants {n : ℕ} {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    0 ≤ -Real.log κ+n*Real.log (r+1) ∧ 0 < Real.log ((r+1)/r) := by
  have hr1 : 1 ≤ r+1 := by linarith
  have hlogκ := Real.log_nonpos hκ.le hκ1
  have hlogr := Real.log_nonneg hr1
  constructor
  · exact add_nonneg (neg_nonneg.mpr hlogκ) (mul_nonneg (Nat.cast_nonneg _) hlogr)
  · apply Real.log_pos
    exact (lt_div_iff₀ hr).mpr (by linarith)

theorem negativeLog_extended_le_thermal {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (x : Fock n) :
    basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) x ≤
      ENNReal.ofReal (-Real.log κ+n*Real.log (r+1))*ENNReal.ofReal (‖x‖^2)+
      ENNReal.ofReal (Real.log ((r+1)/r))*numberVectorMoment x := by
  have hc := thermal_log_constants (n := n) hr hκ hκ1
  have hp1 (j : J) : p j ≤ 1 := hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le)
  have hlog (j : J) : 0 ≤ -Real.log (p j) := neg_nonneg.mpr (Real.log_nonpos (hp j).le (hp1 j))
  by_cases hx : FiniteVectorEnergy x
  · have h := negativeLog_le_thermal ρ hr hκ hκ1 hle b p hp hs he x hx
    have hE : 0 ≤ vectorEnergy x := tsum_nonneg (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    rw [basisMoment_ofReal b _ hlog x h.1, numberVectorMoment_ofReal x hx,
      ← ENNReal.ofReal_mul hc.1, ← ENNReal.ofReal_mul hc.2.le, ← ENNReal.ofReal_add (mul_nonneg hc.1 (sq_nonneg _)) (mul_nonneg hc.2.le hE)]
    exact ENNReal.ofReal_le_ofReal h.2
  · have he : numberVectorMoment x = ⊤ := not_lt_top_iff.mp (fun h => hx ((finiteVectorEnergy_iff x).mpr h))
    rw [he, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc.2).ne', add_top]
    exact le_top

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
open QuantumTrace


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.negativeLog_extended_le_thermal := @_root_.OAI.EntropyPhotonNumber.negativeLog_extended_le_thermal
