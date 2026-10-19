-- Prove2me | solution 2 for OAI.GaussianPropeller.Reduction.exists_unique_scoreCell
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:35:34.490341+00:00
-- url     : https://prove2.me/submissions/eef7a917-8be1-446c-bd22-3e2845a16751

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Dual.lean:L110-L138
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.exists_unique_scoreCell. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

-- ---- from OAI.Probability.GaussianPropeller.Dual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

theorem le_scoreMax (v : Fin k → Space d) (i : Fin k) (x : Space d) :
    ⟪v i, x⟫ ≤ scoreMax v x := by
  exact Finset.le_sup' (fun j => ⟪v j, x⟫) (Finset.mem_univ i)

theorem exists_scoreMax (v : Fin k → Space d) (x : Space d) :
    ∃ i, ⟪v i, x⟫ = scoreMax v x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)
  exact ⟨i, hi.symm⟩

theorem exists_unique_scoreCell (v : Fin k → Space d) (x : Space d) :
    ∃! i, x ∈ scoreCell v i := by
  classical
  let s := Finset.univ.filter (fun i => ⟪v i, x⟫ = scoreMax v x)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := exists_scoreMax v x
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i := s.min' hs
  have hmax : ⟪v i, x⟫ = scoreMax v x := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hi : x ∈ scoreCell v i := by
    constructor
    · intro j
      rw [hmax]
      exact le_scoreMax v j x
    · intro j hji
      have hle : ⟪v j, x⟫ ≤ ⟪v i, x⟫ := hmax ▸ le_scoreMax v j x
      apply lt_of_le_of_ne hle
      intro heq
      have hmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, heq.trans hmax⟩
      exact (not_lt_of_ge (s.min'_le j hmem)) hji
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply le_antisymm
  · by_contra h
    have hlt : i < j := lt_of_not_ge h
    exact (not_lt_of_ge (hi.1 j)) (hj.2 i hlt)
  · by_contra h
    have hlt : j < i := lt_of_not_ge h
    exact (not_lt_of_ge (hj.1 i)) (hi.2 j hlt)

end Reduction

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.exists_unique_scoreCell := @_root_.OAI.GaussianPropeller.Reduction.exists_unique_scoreCell
