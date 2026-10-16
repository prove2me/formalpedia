-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteCoupling.exists_positive_ge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:41:41.597416+00:00
-- url     : https://prove2.me/submissions/a8a2d352-4a32-4b04-bca1-b97f7b47b3d2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean:L356-L373
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteCoupling.exists_positive_ge. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling

-- ---- from OAI.Combinatorics.CliqueFree.FiniteCoupling ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteCoupling
universe z
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2
lemma exists_positive_ge {q : I → ℝ} (hq : Law q) (f : I → ℝ) {L : ℝ}
    (hL : L ≤ ∑ i, q i * f i) : ∃ i, 0 < q i ∧ L ≤ f i := by
  by_contra h
  have hf : ∀ i, 0 < q i → f i < L := by
    intro i hi
    by_contra hn
    exact h ⟨i, hi, le_of_not_gt hn⟩
  obtain ⟨i, _, hi⟩ := (sum_pos_iff_of_nonneg (fun j (_ : j ∈ univ) ↦ hq.1 j)).1
    (show 0 < ∑ j, q j by rw [hq.2]; norm_num)
  have hlt : (∑ j, q j * f j) < ∑ j, q j * L := by
    apply sum_lt_sum
    · intro j _
      rcases (hq.1 j).eq_or_lt with hj | hj
      · simp [← hj]
      · exact (mul_lt_mul_of_pos_left (hf j hj) hj).le
    · exact ⟨i, mem_univ i, mul_lt_mul_of_pos_left (hf i hi) hi⟩
  rw [← sum_mul, hq.2, one_mul] at hlt
  linarith

end FiniteCoupling

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteCoupling
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteCoupling.exists_positive_ge.{u} := @_root_.OAI.CliqueFreeIndependence.FiniteCoupling.exists_positive_ge.{u}
