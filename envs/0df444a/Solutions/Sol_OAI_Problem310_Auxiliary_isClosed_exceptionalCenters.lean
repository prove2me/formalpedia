-- Prove2me | solution 1 for OAI.Problem310.Auxiliary.isClosed_exceptionalCenters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:44:36.705752+00:00
-- url     : https://prove2.me/submissions/be05de0d-f7ef-48fa-b9f8-87f15d50d7df

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean:L17-L40
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.isClosed_exceptionalCenters. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters ----
namespace OAI

noncomputable section

open Set Filter Topology

namespace Problem310.Auxiliary

section

/-- Compactness of the normalized scale interval makes the exceptional centers closed. -/
theorem isClosed_exceptionalCenters (B : Set ℝ) (hB : IsOpen B)
    (N : Set ℕ) (a : ℕ → ℝ) : IsClosed (exceptionalCenters B N a) := by
  let K := Icc (1 : ℝ) 2
  let S : Set (ℝ × K) := {z | ∀ n ∈ N, z.1 + (z.2 : ℝ) * a n ∉ B}
  have hS : IsClosed S := by
    have heq : S = ⋂ n ∈ N, {z : ℝ × K | z.1 + (z.2 : ℝ) * a n ∉ B} := by
      ext z
      simp [S]
    rw [heq]
    refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
    exact hB.isClosed_compl.preimage (continuous_fst.add
      ((continuous_subtype_val.comp continuous_snd).mul_const (a n)))
  have hK : IsCompact K := isCompact_Icc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hproj : IsClosed (Prod.fst '' S) := isClosedMap_fst_of_compactSpace S hS
  convert hproj using 1
  ext x
  simp only [exceptionalCenters, S, K, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨(x, ⟨t, ht⟩), h, rfl⟩
  · rintro ⟨⟨y, t, ht⟩, h, rfl⟩
    exact ⟨t, ht, h⟩

open Set Filter Topology MeasureTheory Metric

end

open Set Filter Topology MeasureTheory

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.Problem310.Auxiliary.isClosed_exceptionalCenters := @_root_.OAI.Problem310.Auxiliary.isClosed_exceptionalCenters
