-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.beamOutput_powerMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:14:45.800674+00:00
-- url     : https://prove2.me/submissions/942bc2d0-0f23-49ac-8ecb-cf9d4bbddc3e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean:L917-L962
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.beamOutput_powerMoment_le. The node keeps its source
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

theorem tensor_mul_moment (w : A → ℝ≥0∞) (u : B → ℝ≥0∞) (x : H A) (y : H B) :
    vectorMoment (fun ab : A × B => w ab.1*u ab.2) (tensor x y) =
      vectorMoment w x*vectorMoment u y := by
  change (∑' ab : A × B, (w ab.1*u ab.2)*ENNReal.ofReal (‖x ab.1*y ab.2‖^2)) = _
  simp only [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.tsum_prod']
  simp_rw [mul_mul_mul_comm (w _) (u _) (ENNReal.ofReal _) (ENNReal.ofReal _)]
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, vectorMoment]

theorem ensemble_tensor_mul_moment [DecidableEq A] [DecidableEq B]
    {v : I → H A} {z : J → H B}
    (hv : Summable (fun i => ‖v i‖^2)) (hz : Summable (fun j => ‖z j‖^2))
    (w : A → ℝ≥0∞) (u : B → ℝ≥0∞) :
    (∑' ij : I × J, vectorMoment (fun ab : A × B => w ab.1*u ab.2) (tensor (v ij.1) (z ij.2))) =
      matrixMoment w (TraceEnsemble.operator v)*matrixMoment u (TraceEnsemble.operator z) := by
  simp only [tensor_mul_moment, ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  rw [matrixMoment_ensemble hv, matrixMoment_ensemble hz]

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

theorem beamOutput_powerMoment_le {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (m : ℕ) (ρA ρB : State n) :
    powerMoment m (beamOutput η hη ρA ρB) ≤ powerMoment m ρA*powerMoment m ρB := by
  change matrixMoment _ (partialTrace (mixedVector η hη ρA ρB)) ≤ _
  rw [partialTrace_moment (mixedVector_norm η hη ρA ρB).summable]
  calc
    _ ≤ ∑' a, vectorMoment (fun ab : PairedIndex n =>
        (1+((totalNumber (fun j => ab.1 j+ab.2 j)) : ℝ≥0∞))^m) (mixedVector η hη ρA ρB a) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro ab
      apply mul_le_mul' _ le_rfl
      apply pow_le_pow_left'
      simp only [totalNumber, Finset.sum_add_distrib, Nat.cast_add]
      exact add_le_add_right le_self_add 1
    _ = ∑' a : PairedIndex n, vectorMoment (fun ab : PairedIndex n =>
        (1+((totalNumber (fun j => ab.1 j+ab.2 j)) : ℝ≥0∞))^m)
        (tensor (rootColumn ρA a.1) (rootColumn ρB a.2)) := by
      congr 1
      funext a
      exact beam_vector_moment η hη _ (fun k => (1+(totalNumber k : ℝ≥0∞))^m)
    _ ≤ ∑' a : PairedIndex n, vectorMoment (fun ab : PairedIndex n =>
        (1+(totalNumber ab.1 : ℝ≥0∞))^m*(1+(totalNumber ab.2 : ℝ≥0∞))^m)
        (tensor (rootColumn ρA a.1) (rootColumn ρB a.2)) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro ab
      apply mul_le_mul' _ le_rfl
      dsimp only
      rw [← mul_pow]
      apply pow_le_pow_left'
      simp only [totalNumber, Finset.sum_add_distrib, Nat.cast_add]
      rw [add_mul, one_mul, mul_add, mul_one]
      rw [← add_assoc]
      calc
        1+((∑ j, ab.1 j : ℕ):ℝ≥0∞)+(∑ j, ab.2 j : ℕ) ≤
          1+((∑ j, ab.1 j : ℕ):ℝ≥0∞)+(∑ j, ab.2 j : ℕ)+
            ((∑ j, ab.1 j : ℕ):ℝ≥0∞)*(∑ j, ab.2 j : ℕ) := le_self_add
        _ = _ := by ac_rfl
    _ = powerMoment m ρA*powerMoment m ρB := by
      rw [ensemble_tensor_mul_moment (rootColumn_norm ρA).summable (rootColumn_norm ρB).summable
        (fun k => (1+(totalNumber k : ℝ≥0∞))^m) (fun k => (1+(totalNumber k : ℝ≥0∞))^m),
        rootColumn_operator, rootColumn_operator]
      rfl

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
open TensorLp


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.beamOutput_powerMoment_le := @_root_.OAI.EntropyPhotonNumber.beamOutput_powerMoment_le
