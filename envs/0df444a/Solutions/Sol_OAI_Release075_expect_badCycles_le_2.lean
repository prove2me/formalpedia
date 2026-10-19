-- Prove2me | solution 2 for OAI.Release075.expect_badCycles_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:15:12.153999+00:00
-- url     : https://prove2.me/submissions/1e70094d-45c0-4c6e-ae1c-68357b46aafa

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L255-L278
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.expect_badCycles_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_CycleCandidate_expect_occurs

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

/-- Expected cycle bound before specializing the finite field cardinalities. -/
theorem expect_badCycles_le [Fintype A] [Fintype K] [Fintype V]
    [Fintype (Projectivization K V)] [Nontrivial V]
    (S : Finset V) (σ : A → A) :
    (𝔼 ω : S → Projectivization K V, ((badCycles S σ ω).card : ℝ)) ≤
      (Fintype.card V : ℝ)^Fintype.card A * (Fintype.card K : ℝ)^Fintype.card A *
        (1 / Fintype.card (Projectivization K V) : ℝ)^Fintype.card A := by
  have hcard : Fintype.card (CycleCandidate (K := K) S σ) ≤
      Fintype.card V ^ Fintype.card A * Fintype.card K ^ Fintype.card A := by
    simpa [CycleCandidate] using Fintype.card_subtype_le
      (fun c : (A → V) × (A → K) => Function.Injective c.1 ∧
        (∀ a, c.1 (σ a) ≠ c.1 a) ∧ (∀ a, candidateMark σ c.1 c.2 a ∈ S) ∧
        Function.Injective (candidateMark σ c.1 c.2))
  calc
    _ = ∑ c : CycleCandidate (K := K) S σ, 𝔼 ω : S → Projectivization K V,
        if c.Occurs ω then (1 : ℝ) else 0 := by
      simp only [badCycles, ← Finset.sum_boole]
      exact Finset.expect_sum_comm _ _ _
    _ = (Fintype.card (CycleCandidate (K := K) S σ) : ℝ) *
        (1 / Fintype.card (Projectivization K V) : ℝ)^Fintype.card A := by
      simp only [CycleCandidate.expect_occurs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard

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


theorem solution : type_of% @_root_.OAI.Release075.expect_badCycles_le := @_root_.OAI.Release075.expect_badCycles_le
