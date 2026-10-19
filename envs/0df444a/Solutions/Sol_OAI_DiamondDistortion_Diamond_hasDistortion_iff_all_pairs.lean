-- Prove2me | solution 1 for OAI.DiamondDistortion.Diamond.hasDistortion_iff_all_pairs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:27:27.073102+00:00
-- url     : https://prove2.me/submissions/bb3b1b74-ed60-4e46-a696-75c89b28217e

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
import Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable
import Definitions.Def_OAI_Analysis_DiamondDistortion_ModelMaps
import Definitions.Def_OAI_Analysis_DiamondDistortion_EquivalentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_UpperFunction
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveBounds
import Definitions.Def_OAI_Analysis_DiamondDistortion_SignCube
import Definitions.Def_OAI_Analysis_DiamondDistortion_HeadProjections

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Diamond
universe u v
open scoped BigOperators Classical Topology
open Set
open scoped ENNReal
variable {X : Type*} [NormedAddCommGroup X]
def h43_edge : (n : ℕ) → Edge n
  | 0 => ()
  | n + 1 => (h43_edge n, 0, false)

theorem solution {k : ℕ} (f : Vertex k → X) (D s : ℝ) :
    HasDistortion k f D s ↔ 0 < s ∧ ∀ u v,
      s*distance k u v ≤ ‖f u-f v‖ ∧ ‖f u-f v‖ ≤ D*s*distance k u v := by
  have hne : endpoint k (h43_edge k) false ≠ endpoint k (h43_edge k) true := by
    cases k with
    | zero => simp [endpoint]
    | succ n => simp [h43_edge, endpoint]
  have hadj : (graph k).Adj (endpoint k (h43_edge k) false) (endpoint k (h43_edge k) true) := by
    rw [graph, SimpleGraph.fromRel_adj]; exact ⟨hne, Or.inl ⟨_, rfl, rfl⟩⟩
  have hd : distance k (endpoint k (h43_edge k) false) (endpoint k (h43_edge k) true) = 1 / 2 ^ k := by
    rw [distance, SimpleGraph.dist_eq_one_iff_adj.mpr hadj]; simp
  constructor
  · rintro ⟨_, hs, h⟩; exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    refine ⟨?_, hs, h⟩
    obtain ⟨h1, h2⟩ := h (endpoint k (h43_edge k) false) (endpoint k (h43_edge k) true)
    rw [hd] at h1 h2
    have hp : 0 < s * (1 / 2 ^ k) := by positivity
    by_contra hD
    push_neg at hD
    nlinarith [mul_lt_mul_of_pos_right hD hp]

