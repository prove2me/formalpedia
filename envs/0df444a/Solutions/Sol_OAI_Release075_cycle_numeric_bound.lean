-- Prove2me | solution 1 for OAI.Release075.cycle_numeric_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:30:07.060985+00:00
-- url     : https://prove2.me/submissions/64fa2350-c834-4572-92a9-6e9ed4732a42

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L745-L758
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.cycle_numeric_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

end CycleCandidate

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

end Degrees

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

end AlterationMean

/-- A concrete bound for every short-cycle contribution. -/
theorem cycle_numeric_bound {q J : ℝ} (hq : 1 ≤ q) (hJ : q^19 ≤ J)
    {s : ℕ} (hs : s ≤ 6) : (q^20)^s * q^s * (1/J)^s ≤ q^12 := by
  have hq0 : 0 < q := by linarith
  have hJ0 : 0 < J := (pow_pos hq0 19).trans_le hJ
  have hf : q^20 * q / J ≤ q^2 := by
    apply (div_le_iff₀ hJ0).mpr
    have hj := mul_le_mul_of_nonneg_left hJ (sq_nonneg q)
    convert hj using 1; ring
  calc
    _ = (q^20*q/J)^s := by simp only [div_pow, mul_pow, one_pow]; ring
    _ ≤ (q^2)^s := pow_le_pow_left₀ (by positivity) hf s
    _ = q^(2*s) := by rw [pow_mul]
    _ ≤ q^12 := pow_le_pow_right₀ hq (by omega)

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

end DimensionTwenty

attribute [instance] MarkedLineData.labelFintype

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.Release075.cycle_numeric_bound := @_root_.OAI.Release075.cycle_numeric_bound
