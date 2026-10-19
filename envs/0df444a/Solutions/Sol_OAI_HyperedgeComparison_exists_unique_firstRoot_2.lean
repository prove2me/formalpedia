-- Prove2me | solution 2 for OAI.HyperedgeComparison.exists_unique_firstRoot
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:40:57.484157+00:00
-- url     : https://prove2.me/submissions/1a0d045c-7499-4037-9152-11e1a9387c2a

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L296-L315
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.exists_unique_firstRoot. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

theorem adj_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Adj H ω D x y) : Adj H ω D y x := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd, hy, hx⟩

theorem connected_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Connected H ω D x y) : Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hxy ih => exact ih.head (adj_symm hxy)

theorem connected_refl (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) :
    Connected H ω D x x := .refl

theorem connected_trans {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y z : V}
    (hxy : Connected H ω D x y) (hyz : Connected H ω D y z) :
    Connected H ω D x z := hxy.trans hyz

theorem firstRoot_iff {n : ℕ} {H : Hypergraph V E} {x : Fin n → V} {ω : E → Bool}
    {D : Set V} {k i : Fin n} :
    firstRoot H x ω D k i ↔ Connected H ω D (x k) (x i) ∧
      ∀ j < k, ¬Connected H ω D (x j) (x i) := by
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨hc, ?_⟩
    intro j hj hji
    exact Set.disjoint_left.mp hd (connected_trans hc (connected_symm hji)) ⟨j, hj, rfl⟩
  · rintro ⟨hc, hf⟩
    refine ⟨Set.disjoint_left.mpr ?_, hc⟩
    rintro y hy ⟨j, hj, rfl⟩
    exact hf j hj (connected_trans (connected_symm hy) hc)

theorem exists_unique_firstRoot {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (D : Set V) (i : Fin n) : ∃! k, firstRoot H x ω D k i := by
  classical
  let J := Finset.univ.filter (fun j => Connected H ω D (x j) (x i))
  have hJ : J.Nonempty := ⟨i, by simp [J, connected_refl]⟩
  let k := J.min' hJ
  have hkJ : k ∈ J := Finset.min'_mem J hJ
  have hkc : Connected H ω D (x k) (x i) := (Finset.mem_filter.mp hkJ).2
  have hf : firstRoot H x ω D k i := by
    apply firstRoot_iff.mpr
    refine ⟨hkc, ?_⟩
    intro j hj hc
    have hkj : k ≤ j := Finset.min'_le J j (by simp [J, hc])
    exact (not_le_of_gt hj) hkj
  refine ⟨k, hf, ?_⟩
  intro j hj
  apply le_antisymm
  · by_contra h
    exact (firstRoot_iff.mp hj).2 k (lt_of_not_ge h) hkc
  · exact Finset.min'_le J j (by simp [J, (firstRoot_iff.mp hj).1])

section FiniteLaw
variable [Fintype E]

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

end OAI

-- ---- platform node ----
open OAI OAI.HyperedgeComparison
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.exists_unique_firstRoot.{uE,uV} := @_root_.OAI.HyperedgeComparison.exists_unique_firstRoot.{uE,uV}
