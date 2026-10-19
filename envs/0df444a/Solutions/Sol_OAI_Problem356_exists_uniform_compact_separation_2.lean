-- Prove2me | solution 2 for OAI.Problem356.exists_uniform_compact_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:09:42.665523+00:00
-- url     : https://prove2.me/submissions/0a82b5f2-40dc-47ca-843a-092beda267c8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CompactSeparation.lean:L11-L37
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.exists_uniform_compact_separation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

-- ---- from OAI.Analysis.CoulombTransport.CompactSeparation ----
namespace OAI

universe uAlpha uIndex

noncomputable section

namespace Problem356

/-- Finitely many pairwise disjoint compact components in a metric space have
one positive separation bound. Empty components and an empty index type are
allowed, so no auxiliary nonemptiness assumptions are needed. -/
theorem exists_uniform_compact_separation {α : Type uAlpha} {ι : Type uIndex} [MetricSpace α] [Finite ι]
    (K : ι → Set α) (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, eta ≤ dist x y := by
  let P := {p : ι × ι // p.1 ≠ p.2}
  let S : Set (α × α) := ⋃ p : P, K p.val.1 ×ˢ K p.val.2
  have hS : IsCompact S :=
    isCompact_iUnion (fun p : P => (hcompact p.val.1).prod (hcompact p.val.2))
  have hmem (i j : ι) (hij : i ≠ j) (x y : α) (hx : x ∈ K i) (hy : y ∈ K j) :
      (x, y) ∈ S := by
    exact Set.mem_iUnion.mpr ⟨⟨(i, j), hij⟩, hx, hy⟩
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hpmin⟩ := hS.exists_isMinOn hne continuous_dist.continuousOn
    have hpne : p.1 ≠ p.2 := by
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hp
      intro heq
      exact Set.disjoint_left.mp (hdisjoint q.property) hq.1 (heq ▸ hq.2)
    refine ⟨dist p.1 p.2, dist_pos.mpr hpne, ?_⟩
    intro i j hij x hx y hy
    exact hpmin (hmem i j hij x y hx hy)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i j hij x hx y hy
    exact False.elim (hne ⟨(x, y), hmem i j hij x y hx hy⟩)

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356


theorem solution.{uAlpha,uIndex} : type_of% @_root_.OAI.Problem356.exists_uniform_compact_separation.{uAlpha,uIndex} := @_root_.OAI.Problem356.exists_uniform_compact_separation.{uAlpha,uIndex}
