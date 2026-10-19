-- Prove2me | solution 1 for OAI.RecursivePotentials.ZeroTreeSpace.tail_eq_coordinate_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:42:54.715811+00:00
-- url     : https://prove2.me/submissions/4fdbe7af-fbeb-4263-9d39-bb477a8ebd52

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean:L201-L216
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.ZeroTreeSpace.tail_eq_coordinate_kernel. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

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

lemma inclusion_injective : Function.Injective (inclusion T) := by
  intro x y h
  have he : inclusion T (x - y) = 0 := by rw [map_sub, h, sub_self]
  have hn := norm_inclusion T (x - y)
  rw [he, norm_zero] at hn
  have hz : ‖x - y‖ = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma inclusion_projection (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    inclusion T (projection T H hH x) = TreeSpace.projection T H hH (inclusion T x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v => simp only [projection_coe, inclusion_coe, TreeSpace.projection_coe,
      ZeroTreeVector.inclusion_projection]

lemma include_tail (H : Finset ι) (hH : T.Initial H) (z : ZeroTreeSpace T)
    (hz : z ∈ tail T H hH) : inclusion T z ∈ TreeSpace.tail T H hH := by
  change TreeSpace.projection T H hH (inclusion T z) = 0
  rw [← inclusion_projection, show projection T H hH z = 0 from hz, map_zero]

end ZeroTreeSpace

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma tail_eq_coordinate_kernel (H : Finset ι) (hH : T.Initial H) :
    tail T H hH = (headCoordinates T H).ker := by
  ext x
  constructor
  · intro hx
    have h := include_tail T H hH x hx
    rw [TreeSpace.tail_eq_coordinate_kernel] at h
    exact h
  · intro hx
    have h : inclusion T x ∈ TreeSpace.tail T H hH := by
      rw [TreeSpace.tail_eq_coordinate_kernel]
      exact hx
    change projection T H hH x = 0
    apply inclusion_injective T
    rw [inclusion_projection, map_zero]
    exact h

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


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.ZeroTreeSpace.tail_eq_coordinate_kernel.{uIndex} := @_root_.OAI.RecursivePotentials.ZeroTreeSpace.tail_eq_coordinate_kernel.{uIndex}
