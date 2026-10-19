-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.coordinateTest_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:25:03.62956+00:00
-- url     : https://prove2.me/submissions/5e3c3d8d-1b05-44d0-8c3d-1e2ac6122b62

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean:L797-L815
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.coordinateTest_pairing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma coordinateTest_not_mem (K : Finset ι) (a : T.Coordinates K)
    {v : ι} (hv : v ∉ K) : T.coordinateTest K a v = 0 := by simp [coordinateTest, hv]

variable {T}

variable (T)

lemma coordinateTest_pairing (K : Finset ι) (a : T.Coordinates K) (x : T.Dual) :
    x (T.finiteEmbedding (T.coordinateTest K a)) =
      ∑ v : K, a v * x (T.unitVector v.val) := by
  classical
  rw [finiteEmbedding_apply, dual_coe_apply]
  change (∑ v ∈ (T.coordinateTest K a).support,
    T.coordinateTest K a v * x (T.unitVector v)) = _
  have hs : (T.coordinateTest K a).support ⊆ K := by
    intro v hv
    by_contra hn
    exact Finsupp.mem_support_iff.mp hv (T.coordinateTest_not_mem K a hn)
  calc
    _ = ∑ v ∈ K, T.coordinateTest K a v * x (T.unitVector v) := by
      apply Finset.sum_subset hs
      intro v _ hv
      rw [Finsupp.notMem_support_iff.mp hv, zero_mul]
    _ = ∑ v : K, T.coordinateTest K a v.val * x (T.unitVector v.val) :=
      (Finset.sum_coe_sort K _).symm
    _ = _ := by simp only [coordinateTest_mem]

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.coordinateTest_pairing := @_root_.OAI.DiamondDistortion.SegmentSystem.coordinateTest_pairing
