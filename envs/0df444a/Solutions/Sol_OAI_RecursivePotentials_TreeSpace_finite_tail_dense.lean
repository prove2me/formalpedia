-- Prove2me | solution 1 for OAI.RecursivePotentials.TreeSpace.finite_tail_dense
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:29:53.528574+00:00
-- url     : https://prove2.me/submissions/72c63c7e-6f60-4aee-9586-5fadafc13e65

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean:L867-L886
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.TreeSpace.finite_tail_dense. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

-- ---- from OAI.Analysis.RecursivePotentials.TreeGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma projection_idem (H : Finset ι) (hH : T.Initial H) (v : TreeVector T) :
    projection T H hH (projection T H hH v) = projection T H hH v := by
  change ι →₀ ℝ at v
  apply Finsupp.ext
  intro s
  change T.projectHead H (T.projectHead H v) s = T.projectHead H v s
  simp [FiniteRootedTree.projectHead, Finsupp.filter_apply]
  intro hs hs'
  exact (hs hs').elim

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma projection_contracts (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T) :
    ‖projection T H hH x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (continuous_norm.comp (projection T H hH).continuous) continuous_norm
  | ih v => simpa only [projection_coe, Completion.norm_coe] using
      TreeVector.projection_contracts T H hH v

theorem finite_tail_dense (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T)
    (hx : x ∈ tail T H hH) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : TreeVector T, TreeVector.projection T H hH v = 0 ∧
      ‖(v : TreeSpace T) - x‖ < ε := by
  have hx0 : projection T H hH x = 0 := hx
  obtain ⟨v, hv⟩ := Completion.denseRange_coe.exists_dist_lt x (half_pos hε)
  let w : TreeVector T := v - TreeVector.projection T H hH v
  refine ⟨w, ?_, ?_⟩
  · change TreeVector.projection T H hH (v - TreeVector.projection T H hH v) = 0
    rw [map_sub, TreeVector.projection_idem, sub_self]
  · have he : (w : TreeSpace T) - x =
        ((v : TreeSpace T) - x) - projection T H hH ((v : TreeSpace T) - x) := by
      change (↑(v - TreeVector.projection T H hH v) : TreeSpace T) - x = _
      simp only [Completion.coe_sub, ← projection_coe, map_sub, hx0, sub_zero]
      abel
    rw [he]
    have hp := projection_contracts T H hH ((v : TreeSpace T) - x)
    have hv' : ‖(v : TreeSpace T) - x‖ < ε / 2 := by
      simpa only [dist_comm x, dist_eq_norm] using hv
    exact (norm_sub_le _ _).trans_lt (by linarith)

end TreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace CofiniteSubspace

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end CofiniteSubspace

section Moduli

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Moduli

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
open scoped BigOperators
open UniformSpace


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.TreeSpace.finite_tail_dense.{uIndex} := @_root_.OAI.RecursivePotentials.TreeSpace.finite_tail_dense.{uIndex}
