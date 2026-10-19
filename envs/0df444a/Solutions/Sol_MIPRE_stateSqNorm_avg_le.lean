-- Prove2me | solution 1 for MIPRE.stateSqNorm_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:36:40.829128+00:00
-- url     : https://prove2.me/submissions/cee9b505-3c3c-4c28-a417-0c0bf7272538

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/StateDistance.lean (solution of MIPRE.stateSqNorm_avg_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset ComplexOrder Matrix
variable {n : Type*} [Fintype n]
/-- `𝔼_μ √f ≤ √(𝔼_μ 1) · √(𝔼_μ f)`, which for a probability distribution is Jensen's
inequality for the square root. It is Cauchy--Schwarz applied to `√μ` and `√(μ f)`. -/
theorem sum_mul_sqrt_le {ι : Type*} (s : Finset ι) (μ f : ι → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, μ i * √(f i) ≤ √(∑ i ∈ s, μ i) * √(∑ i ∈ s, μ i * f i) := by
  have key : ∀ i, μ i * √(f i) = √(μ i) * √(μ i * f i) := by
    intro i
    rw [Real.sqrt_mul (hμ i), ← mul_assoc, Real.mul_self_sqrt (hμ i)]
  rw [Finset.sum_congr rfl fun i _ => key i]
  exact Real.sum_sqrt_mul_sqrt_le _ hμ (fun i => mul_nonneg (hμ i) (hf i))
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateVec_sum {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι) (f : ι → Matrix dA dA ℂ) :
    stateVec ψ (∑ i ∈ s, f i) = ∑ i ∈ s, stateVec ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, stateVec_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateNorm ψ M :=
  norm_nonneg _
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateSqNorm ψ M :=
  sq_nonneg _
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem sqrt_stateSqNorm (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    Real.sqrt (stateSqNorm ψ M) = stateNorm ψ M :=
  Real.sqrt_sq (stateNorm_nonneg ψ M)
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateNorm_smul (ψ : dA × dB → ℂ) (c : ℂ) (M : Matrix dA dA ℂ) :
    stateNorm ψ (c • M) = ‖c‖ * stateNorm ψ M := by
  rw [stateNorm, stateNorm, stateVec_smul, norm_smul]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateNorm_sum_le {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (f : ι → Matrix dA dA ℂ) :
    stateNorm ψ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, stateNorm ψ (f i) := by
  rw [stateNorm, stateVec_sum]
  exact norm_sum_le _ _
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateDist_nonneg {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (ψ : dA × dB → ℂ)
    (A B : X → Matrix dA dA ℂ) : 0 ≤ stateDist μ ψ A B :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (stateSqNorm_nonneg ψ _)
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (ψ : dA × dB → ℂ) (A B : X → Matrix dA dA ℂ) (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) :
    stateSqNorm ψ ((∑ x, ((μ x : ℂ) * α x) • A x) - ∑ x, ((μ x : ℂ) * α x) • B x)
      ≤ stateDist μ ψ A B := by
  classical
  have hsub : (∑ x, ((μ x : ℂ) * α x) • A x) - (∑ x, ((μ x : ℂ) * α x) • B x)
      = ∑ x, ((μ x : ℂ) * α x) • (A x - B x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => (smul_sub _ _ _).symm
  have htri : stateNorm ψ (∑ x, ((μ x : ℂ) * α x) • (A x - B x))
      ≤ ∑ x, μ x * stateNorm ψ (A x - B x) := by
    refine (stateNorm_sum_le ψ Finset.univ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [stateNorm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (stateNorm_nonneg ψ _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ0 x)]
    calc μ x * ‖α x‖ ≤ μ x * 1 := mul_le_mul_of_nonneg_left (hα x) (hμ0 x)
      _ = μ x := mul_one _
  have hjensen : ∑ x, μ x * stateNorm ψ (A x - B x) ≤ Real.sqrt (stateDist μ ψ A B) := by
    have h := sum_mul_sqrt_le (Finset.univ : Finset X) μ
      (fun x => stateSqNorm ψ (A x - B x)) hμ0 (fun x => stateSqNorm_nonneg ψ _)
    rw [hμ1, Real.sqrt_one, one_mul] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) h
    rw [sqrt_stateSqNorm]
  have hd : 0 ≤ stateDist μ ψ A B := stateDist_nonneg hμ0 ψ A B
  rw [hsub]
  calc stateSqNorm ψ (∑ x, ((μ x : ℂ) * α x) • (A x - B x))
      ≤ Real.sqrt (stateDist μ ψ A B) ^ 2 :=
        pow_le_pow_left₀ (stateNorm_nonneg ψ _) (htri.trans hjensen) 2
    _ = stateDist μ ψ A B := Real.sq_sqrt hd
end MIPRE
