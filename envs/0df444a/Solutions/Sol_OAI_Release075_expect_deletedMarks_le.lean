-- Prove2me | solution 1 for OAI.Release075.expect_deletedMarks_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:26:11.972989+00:00
-- url     : https://prove2.me/submissions/2c165272-953b-4bb6-86f4-ebefed758d98

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L662-L685
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.expect_deletedMarks_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_expect_badCycles_le

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

theorem deletedMarks_card_le (S : Finset V) (ω : S → Projectivization K V) :
    (deletedMarks S ω).card ≤ 6 * ∑ s ∈ Finset.Icc 2 6, (badCycles S (finRotate s) ω).card := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ s ∈ Finset.Icc 2 6, 6 * (badCycles S (finRotate s) ω).card := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _c ∈ badCycles S (finRotate s) ω, 6 := by
          apply Finset.sum_le_sum
          intro c _
          have hcard : (Finset.univ.image c.marks).card ≤ s := by
            exact Finset.card_image_le.trans (by simp)
          exact hcard.trans (Finset.mem_Icc.mp hs).2
        _ = _ := by simp [mul_comm]
    _ = _ := by rw [Finset.mul_sum]

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

/-- A uniform expectation bound for all removed labels. -/
theorem expect_deletedMarks_le (S : Finset V) (q : ℝ)
    (hcycle : ∀ s ∈ Finset.Icc 2 6,
      (Fintype.card V : ℝ)^s * (Fintype.card K : ℝ)^s *
        (1 / Fintype.card (Projectivization K V) : ℝ)^s ≤ q^12) :
    (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ 30*q^12 := by
  have hpoint (ω : S → Projectivization K V) : ((deletedMarks S ω).card : ℝ) ≤
      6 * ∑ s ∈ Finset.Icc 2 6, ((badCycles S (finRotate s) ω).card : ℝ) := by
    exact_mod_cast deletedMarks_card_le S ω
  calc
    _ ≤ 𝔼 ω : S → Projectivization K V,
        6 * ∑ s ∈ Finset.Icc 2 6, ((badCycles S (finRotate s) ω).card : ℝ) :=
      Finset.expect_le_expect (fun ω _ => hpoint ω)
    _ = 6 * ∑ s ∈ Finset.Icc 2 6, 𝔼 ω : S → Projectivization K V,
        ((badCycles S (finRotate s) ω).card : ℝ) := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ 6 * ∑ _s ∈ Finset.Icc 2 6, q^12 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro s hs
      have hh := expect_badCycles_le (K := K) S (finRotate s)
      simp only [Fintype.card_fin] at hh
      exact hh.trans (hcycle s hs)
    _ = 30*q^12 := by norm_num [Finset.sum_const]; ring

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


theorem solution : type_of% @_root_.OAI.Release075.expect_deletedMarks_le := @_root_.OAI.Release075.expect_deletedMarks_le
