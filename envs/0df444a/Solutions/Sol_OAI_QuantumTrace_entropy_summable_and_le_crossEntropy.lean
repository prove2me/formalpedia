-- Prove2me | solution 1 for OAI.QuantumTrace.entropy_summable_and_le_crossEntropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:15:33.785624+00:00
-- url     : https://prove2.me/submissions/66b29ea6-46f3-4b25-8825-8888c0fba4f5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L499-L516
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.entropy_summable_and_le_crossEntropy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Theorems.Thm_OAI_QuantumTrace_negMulLog_le_crossEntropy

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

theorem entropy_summable_and_le_crossEntropy {ι : Type*} (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : HasSum p 1) (hq1 : HasSum q 1)
    (hcross : Summable (fun i => p i * (-Real.log (q i)))) :
    Summable (fun i => Real.negMulLog (p i)) ∧
      (∑' i, Real.negMulLog (p i)) ≤ ∑' i, p i * (-Real.log (q i)) := by
  have hp_le (i : ι) : p i ≤ 1 := by
    simpa only [hp1.tsum_eq] using hp1.summable.le_tsum i (fun j _ => hp j)
  have he0 (i : ι) : 0 ≤ Real.negMulLog (p i) := Real.negMulLog_nonneg (hp i) (hp_le i)
  have hle (i : ι) := negMulLog_le_crossEntropy (hp i) (hq i)
  have hsum := (hq1.summable.sub hp1.summable).add hcross
  have he : Summable (fun i => Real.negMulLog (p i)) :=
    Summable.of_nonneg_of_le he0 hle hsum
  refine ⟨he, ?_⟩
  have hh := he.tsum_le_tsum hle hsum
  rw [(hq1.summable.sub hp1.summable).tsum_add hcross,
    hq1.summable.tsum_sub hp1.summable, hp1.tsum_eq, hq1.tsum_eq] at hh
  simpa only [sub_self, zero_add] using hh

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


theorem solution : type_of% @_root_.OAI.QuantumTrace.entropy_summable_and_le_crossEntropy := @_root_.OAI.QuantumTrace.entropy_summable_and_le_crossEntropy
