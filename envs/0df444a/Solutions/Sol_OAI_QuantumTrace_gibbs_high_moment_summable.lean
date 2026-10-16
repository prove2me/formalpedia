-- Prove2me | solution 1 for OAI.QuantumTrace.gibbs_high_moment_summable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:26:44.649772+00:00
-- url     : https://prove2.me/submissions/2550ac38-ff80-4641-b8a2-a0a5c811e6b7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L1537-L1570
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.gibbs_high_moment_summable. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Theorems.Thm_OAI_QuantumTrace_summable_polynomial_heat

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
end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

end

section
open Filter Topology
variable {ι : Type*}

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

theorem gibbs_high_moment_summable (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    {k b : ℝ} (hk : 0 < k) (hb : 0 ≤ b) (z : J → ℝ)
    (hz0 : ∀ j, 0 ≤ z j)
    (hz : ∀ j, z j ≤ k⁻¹*(u j+b*Real.sqrt (u j/k)))
    (hs : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    Summable (fun j => Real.exp (-u j)*z j^2) := by
  let D := k⁻¹*(1+b*(1+k⁻¹))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound (j : J) : z j ≤ D*(1+u j) := by
    have hr := Real.sqrt_nonneg (u j/k)
    have hr2 := Real.sq_sqrt (div_nonneg (hu j) hk.le)
    have hrle : Real.sqrt (u j/k) ≤ 1+u j/k := by nlinarith [sq_nonneg (Real.sqrt (u j/k)-1)]
    have hrle' : Real.sqrt (u j/k) ≤ (1+k⁻¹)*(1+u j) := by
      rw [div_eq_mul_inv] at hrle ⊢
      nlinarith [hu j, inv_nonneg.mpr hk.le, mul_nonneg (hu j) (inv_nonneg.mpr hk.le)]
    calc
      z j ≤ k⁻¹*(u j+b*Real.sqrt (u j/k)) := hz j
      _ ≤ k⁻¹*((1+u j)+b*((1+k⁻¹)*(1+u j))) :=
        mul_le_mul_of_nonneg_left (add_le_add (by linarith) (mul_le_mul_of_nonneg_left hrle' hb))
          (inv_nonneg.mpr hk.le)
      _ = D*(1+u j) := by dsimp [D]; ring
  have hsq (j : J) : z j^2 ≤ 2*D^2*(1+u j^2) := by
    have h := pow_le_pow_left₀ (hz0 j) (hbound j) 2
    rw [mul_pow] at h
    have hle : (1+u j)^2 ≤ 2*(1+u j^2) := by nlinarith [sq_nonneg (u j-1)]
    have hh := mul_le_mul_of_nonneg_left hle (sq_nonneg D)
    nlinarith
  apply Summable.of_nonneg_of_le (fun j => by positivity) _
    ((summable_polynomial_heat u hu hs).mul_left (2*D^2))
  intro j
  have hh := mul_le_mul_of_nonneg_left (hsq j) (Real.exp_nonneg (-u j))
  calc
    _ ≤ Real.exp (-u j)*(2*D^2*(1+u j^2)) := hh
    _ = _ := by ring

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

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory


theorem solution : type_of% @_root_.OAI.QuantumTrace.gibbs_high_moment_summable := @_root_.OAI.QuantumTrace.gibbs_high_moment_summable
