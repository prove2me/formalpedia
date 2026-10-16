-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.number_form_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:55:10.739777+00:00
-- url     : https://prove2.me/submissions/1e5273a2-25ee-4b48-950c-f73f5db5f042

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L1829-L1845
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.number_form_representation. The node keeps its source
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
import Theorems.Thm_OAI_EntropyPhotonNumber_energyInverse_finiteEnergy
import Theorems.Thm_OAI_QuantumTrace_sliceMoment_bounded_representation

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

variable [CompleteSpace E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

theorem numberVectorMoment_eq {n : ℕ} (x : Fock n) :
    numberVectorMoment x = ∑' k, ENNReal.ofReal ((totalNumber k : ℝ)*‖inner ℂ (numberBasis n k) x‖^2) := by
  simp only [numberVectorMoment, basisMoment, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

theorem numberVectorMoment_ofReal {n : ℕ} (x : Fock n) (hx : FiniteVectorEnergy x) :
    numberVectorMoment x = ENNReal.ofReal (vectorEnergy x) := by
  rw [numberVectorMoment_eq]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hx).symm

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

theorem numberWeight_eq {n : ℕ} (i : NumberIndex n) :
    numberWeight i = 1+(totalNumber i : ℝ) := by
  simp only [numberWeight, totalNumber, Nat.cast_sum]

theorem energyInverse_quadratic {n : ℕ} (x : Fock n) (i : NumberIndex n) :
    numberWeight i*‖energyInverse n x i‖^2 = ‖x i‖^2 := by
  have hW : 0 < numberWeight i := lt_of_lt_of_le (by norm_num) (numberWeight_one_le i)
  change numberWeight i*‖(((rootNumberWeight i^1)⁻¹ : ℝ) : ℂ)*x i‖^2 = _
  rw [pow_one, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    inv_pow, rootNumberWeight, Real.sq_sqrt hW.le]
  rw [← mul_assoc, mul_inv_cancel₀ hW.ne', one_mul]

theorem energyInverse_energy {n : ℕ} (x : Fock n) :
    vectorEnergy (energyInverse n x) ≤ ‖x‖^2 := by
  rw [vectorEnergy, ← (SquareAnalysis.hasSum_square x).tsum_eq]
  apply (energyInverse_finiteEnergy x).tsum_le_tsum _ (SquareAnalysis.hasSum_square x).summable
  intro i
  simp only [numberBasis_apply, numberKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  calc
    _ ≤ numberWeight i*‖energyInverse n x i‖^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [numberWeight_eq]
      linarith
    _ = _ := energyInverse_quadratic x i

end

open QuantumTrace

theorem number_form_representation (n : ℕ) :
    ∃ B : Fock n →L[ℂ] Fock n, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re = numberVectorMoment (energyInverse n x) := by
  have hb (x : Fock n) : sliceMoment (numberBasis n) (fun k => ENNReal.ofReal (totalNumber k))
      (fun _ : Unit => (1 : Fock n →L[ℂ] Fock n)) (energyInverse n x) ≤
      ENNReal.ofReal (1*‖x‖^2) := by
    simp only [sliceMoment, one_apply_eq_self, tsum_fintype,
      Fintype.sum_unique, ENNReal.ofReal_natCast]
    change numberVectorMoment (energyInverse n x) ≤ _
    rw [numberVectorMoment_ofReal _ (energyInverse_finiteEnergy x), one_mul]
    exact ENNReal.ofReal_le_ofReal (energyInverse_energy x)
  obtain ⟨B,hB,h⟩ := sliceMoment_bounded_representation (numberBasis n)
    (fun k => (totalNumber k : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun _ : Unit => (1 : Fock n →L[ℂ] Fock n)) (energyInverse n) (by norm_num : (0:ℝ) ≤ 1) hb
  refine ⟨B,hB,fun x => ?_⟩
  simpa only [sliceMoment, one_apply_eq_self, tsum_fintype,
    Fintype.sum_unique, ENNReal.ofReal_natCast, numberVectorMoment] using h x

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


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.number_form_representation := @_root_.OAI.EntropyPhotonNumber.number_form_representation
