-- Prove2me | solution 1 for OAI.RecursivePotentials.ZeroTreeSpace.finite_tail_dense
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:44:25.443799+00:00
-- url     : https://prove2.me/submissions/52f63b67-731e-4055-9f78-d63a8d76c880

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean:L223-L242
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.ZeroTreeSpace.finite_tail_dense. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

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

-- ---- from OAI.Analysis.RecursivePotentials.ZeroRootGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma norm_inclusion (v : ZeroTreeVector T) : ‖inclusion T v‖ = 2 * ‖v‖ := by
  rw [inclusion_apply, norm_half]
  ring

lemma projection_idem (H : Finset ι) (hH : T.Initial H) (v : ZeroTreeVector T) :
    projection T H hH (projection T H hH v) = projection T H hH v := by
  apply toTree_injective T
  change TreeVector.projection T H hH (TreeVector.projection T H hH (toTree T v)) = _
  exact TreeVector.projection_idem T H hH _

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma norm_inclusion (x : ZeroTreeSpace T) : ‖inclusion T x‖ = 2 * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
      rw [inclusion_coe, Completion.norm_coe, Completion.norm_coe]
      exact ZeroTreeVector.norm_inclusion T v

lemma inclusion_projection (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    inclusion T (projection T H hH x) = TreeSpace.projection T H hH (inclusion T x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v => simp only [projection_coe, inclusion_coe, TreeSpace.projection_coe,
      ZeroTreeVector.inclusion_projection]

lemma projection_contracts (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    ‖projection T H hH x‖ ≤ ‖x‖ := by
  have h := TreeSpace.projection_contracts T H hH (inclusion T x)
  rw [← inclusion_projection, norm_inclusion, norm_inclusion] at h
  linarith

end ZeroTreeSpace

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem finite_tail_dense (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T)
    (hx : x ∈ tail T H hH) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ZeroTreeVector T, ZeroTreeVector.projection T H hH v = 0 ∧
      ‖(v : ZeroTreeSpace T) - x‖ < ε := by
  have hx0 : projection T H hH x = 0 := hx
  obtain ⟨v, hv⟩ := Completion.denseRange_coe.exists_dist_lt x (half_pos hε)
  let w : ZeroTreeVector T := v - ZeroTreeVector.projection T H hH v
  refine ⟨w, ?_, ?_⟩
  · change ZeroTreeVector.projection T H hH (v - ZeroTreeVector.projection T H hH v) = 0
    rw [map_sub, ZeroTreeVector.projection_idem, sub_self]
  · have he : (w : ZeroTreeSpace T) - x =
        ((v : ZeroTreeSpace T) - x) - projection T H hH ((v : ZeroTreeSpace T) - x) := by
      change (↑(v - ZeroTreeVector.projection T H hH v) : ZeroTreeSpace T) - x = _
      simp only [Completion.coe_sub, ← projection_coe, map_sub, hx0, sub_zero]
      abel
    rw [he]
    have hp := projection_contracts T H hH ((v : ZeroTreeSpace T) - x)
    have hv' : ‖(v : ZeroTreeSpace T) - x‖ < ε / 2 := by
      simpa only [dist_comm x, dist_eq_norm] using hv
    exact (norm_sub_le _ _).trans_lt (by linarith)

end ZeroTreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.ZeroTreeSpace
open scoped BigOperators
open UniformSpace


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.ZeroTreeSpace.finite_tail_dense.{uIndex} := @_root_.OAI.RecursivePotentials.ZeroTreeSpace.finite_tail_dense.{uIndex}
