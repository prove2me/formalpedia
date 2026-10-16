-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.logarithmic_slice_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:53:20.458368+00:00
-- url     : https://prove2.me/submissions/ba6aedbe-d1ff-4dff-a50e-ef5ae32f3ff6

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L1783-L1823
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.logarithmic_slice_representation. The node keeps its source
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
import Theorems.Thm_OAI_EntropyPhotonNumber_negativeLog_extended_le_thermal
import Theorems.Thm_OAI_QuantumTrace_sliceMoment_bounded_representation

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
theorem diagonalMap_norm_le (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    {C : ℝ} (hC : 0 ≤ C) (hab : ∀ i, ‖a i‖ ≤ C) : ‖diagonalMap a ha‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have h := lp.norm_mono (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (x := diagonalMap a ha x) (y := (C : ℂ) • x) (fun i => by
      simp only [diagonalMap_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hab i) (norm_nonneg _))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using h

end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

end

section
open Filter Topology
variable {ι : Type*}

theorem inversePower_norm_le (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    ‖inversePower s hs p‖ ≤ 1 := by
  apply diagonalMap_norm_le _ _ (by norm_num)
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity [hs i])]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (hs i))

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open Filter Topology
variable {ι : Type*}

end

section
open Filter Topology

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

end QuantumTrace

end

end OAI

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

theorem thermal_log_constants {n : ℕ} {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    0 ≤ -Real.log κ+n*Real.log (r+1) ∧ 0 < Real.log ((r+1)/r) := by
  have hr1 : 1 ≤ r+1 := by linarith
  have hlogκ := Real.log_nonpos hκ.le hκ1
  have hlogr := Real.log_nonneg hr1
  constructor
  · exact add_nonneg (neg_nonneg.mpr hlogκ) (mul_nonneg (Nat.cast_nonneg _) hlogr)
  · apply Real.log_pos
    exact (lt_div_iff₀ hr).mpr (by linarith)

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

omit [CompleteSpace E] in
theorem sliceMoment_bound (a : HilbertBasis K ℂ E) (b : HilbertBasis J ℂ E)
    (v : K → ℝ≥0∞) (w : J → ℝ≥0∞) (V : I → E →L[ℂ] E) {A B F : ℝ≥0∞}
    (hform : ∀ x, basisMoment b w x ≤ A*ENNReal.ofReal (‖x‖^2)+B*basisMoment a v x)
    (hn : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (he : ∀ x, (∑' i, basisMoment a v (V i x)) ≤
      basisMoment a v x+F*ENNReal.ofReal (‖x‖^2)) (x : E) :
    sliceMoment b w V x ≤ (A+B*F)*ENNReal.ofReal (‖x‖^2)+B*basisMoment a v x := by
  have hN : (∑' i, ENNReal.ofReal (‖V i x‖^2)) = ENNReal.ofReal (‖x‖^2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hn x).summable, (hn x).tsum_eq]
  calc
    _ ≤ ∑' i, (A*ENNReal.ofReal (‖V i x‖^2)+B*basisMoment a v (V i x)) :=
      ENNReal.tsum_le_tsum (fun i => hform (V i x))
    _ = A*ENNReal.ofReal (‖x‖^2)+B*(∑' i, basisMoment a v (V i x)) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hN]
    _ ≤ A*ENNReal.ofReal (‖x‖^2)+B*(basisMoment a v x+F*ENNReal.ofReal (‖x‖^2)) := by
      exact add_le_add le_rfl (mul_le_mul' le_rfl (he x))
    _ = _ := by ring

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

theorem numberVectorMoment_eq_tensor {n : ℕ} (x : Fock n) :
    numberVectorMoment x = vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x := by
  simp only [numberVectorMoment, basisMoment, vectorMoment, numberBasis_apply, numberKet,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

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

theorem energyInverse_norm {n : ℕ} (x : Fock n) : ‖energyInverse n x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖energyInverse n‖*‖x‖ := (energyInverse n).le_opNorm x
    _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right (inversePower_norm_le _ _ _) (norm_nonneg _)
    _ = _ := one_mul _

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

theorem logarithmic_slice_representation {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J I : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (V : I → Fock n →L[ℂ] Fock n) (F : ℝ) (hF : 0 ≤ F)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (hE : ∀ x, (∑' i, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V i x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+ENNReal.ofReal F*ENNReal.ofReal (‖x‖^2)) :
    ∃ B : Fock n →L[ℂ] Fock n, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re =
        sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) V (energyInverse n x) := by
  let A := -Real.log κ+n*Real.log (r+1)
  let D := Real.log ((r+1)/r)
  have hc := thermal_log_constants (n := n) hr hκ hκ1
  have hA : 0 ≤ A := hc.1
  have hD : 0 ≤ D := hc.2.le
  have hp1 (j : J) : p j ≤ 1 := hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le)
  have hlog (j : J) : 0 ≤ -Real.log (p j) := neg_nonneg.mpr (Real.log_nonpos (hp j).le (hp1 j))
  apply sliceMoment_bounded_representation b (fun j => -Real.log (p j)) hlog V (energyInverse n)
    (C := A+D*F+D) (by positivity)
  intro x
  have h := sliceMoment_bound (numberBasis n) b (fun k => (totalNumber k : ℝ≥0∞))
    (fun j => ENNReal.ofReal (-Real.log (p j))) V
    (negativeLog_extended_le_thermal ρ hr hκ hκ1 hle b p hp hs he) hV
    (by intro y; simpa only [← numberVectorMoment_eq_tensor, numberVectorMoment] using hE y) (energyInverse n x)
  have hN : ‖energyInverse n x‖^2 ≤ ‖x‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (energyInverse_norm x) 2
  have hE0 : 0 ≤ vectorEnergy (energyInverse n x) :=
    tsum_nonneg (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  change _ ≤ (ENNReal.ofReal A+ENNReal.ofReal D*ENNReal.ofReal F)*
    ENNReal.ofReal (‖energyInverse n x‖^2)+ENNReal.ofReal D*numberVectorMoment (energyInverse n x) at h
  rw [numberVectorMoment_ofReal _ (energyInverse_finiteEnergy x), ← ENNReal.ofReal_mul hD,
    ← ENNReal.ofReal_add hA (mul_nonneg hD hF),
    ← ENNReal.ofReal_mul (add_nonneg hA (mul_nonneg hD hF)),
    ← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_add
      (mul_nonneg (add_nonneg hA (mul_nonneg hD hF)) (sq_nonneg _)) (mul_nonneg hD hE0)] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hn := mul_le_mul_of_nonneg_left hN (add_nonneg hA (mul_nonneg hD hF))
  have he' := mul_le_mul_of_nonneg_left (energyInverse_energy x) hD
  nlinarith

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
open QuantumTrace TensorLp


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.logarithmic_slice_representation := @_root_.OAI.EntropyPhotonNumber.logarithmic_slice_representation
