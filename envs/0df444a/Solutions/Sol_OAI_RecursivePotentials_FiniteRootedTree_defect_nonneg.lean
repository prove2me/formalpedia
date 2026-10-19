-- Prove2me | solution 1 for OAI.RecursivePotentials.FiniteRootedTree.defect_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:28:21.800187+00:00
-- url     : https://prove2.me/submissions/41f1eb8f-69e5-4aa3-bb57-1cf47248ec51

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean:L410-L422
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.FiniteRootedTree.defect_nonneg. The node keeps its source
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

lemma Upper.add {p q : ι → ℝ} (hpU : T.Upper p) (hqU : T.Upper q)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) : T.Upper (fun s => p s + q s) := by
  intro s
  exact sum_add_sq_le (T.children s) p q (hp s) (hq s) (hpU s) (hqU s)

lemma Upper.smul {p : ι → ℝ} (hpU : T.Upper p) (a : ℝ) :
    T.Upper (fun s => a * p s) := by
  intro s
  simp_rw [mul_pow, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hpU s) (sq_nonneg a)

lemma averaged_feasible (x z : ι → ℝ) :
    T.Upper (fun s => ((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2) ∧
    T.Upper (fun s => ((T.fields (x + z) s).2 + (T.fields (x - z) s).2) / 2) := by
  constructor
  · convert ((T.fields_upper (x + z)).1.add T (T.fields_upper (x - z)).1
      (fun s => (T.fields_nonneg (x + z) s).1)
      (fun s => (T.fields_nonneg (x - z) s).1)).smul T (1 / 2) using 1 ;
      ext s ; ring
  · convert ((T.fields_upper (x + z)).2.add T (T.fields_upper (x - z)).2
      (fun s => (T.fields_nonneg (x + z) s).2)
      (fun s => (T.fields_nonneg (x - z) s).2)).smul T (1 / 2) using 1 ;
      ext s ; ring

lemma defect_nonneg (x z : ι → ℝ) (s : ι) : 0 ≤ T.defect x z s := by
  have h := T.fields_minimal x
    (fun s => ((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2)
    (fun s => ((T.fields (x + z) s).2 + (T.fields (x - z) s).2) / 2)
    (fun s => div_nonneg (add_nonneg (T.fields_nonneg _ s).1 (T.fields_nonneg _ s).1) (by norm_num))
    (fun s => div_nonneg (add_nonneg (T.fields_nonneg _ s).2 (T.fields_nonneg _ s).2) (by norm_num))
    (fun s => by
      have h₁ := T.fields_difference (x + z) s
      have h₂ := T.fields_difference (x - z) s
      simp only [Pi.add_apply, Pi.sub_apply] at h₁ h₂
      linarith)
    (T.averaged_feasible x z).1 (T.averaged_feasible x z).2 s
  exact sub_nonneg.mpr h.1

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

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
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.FiniteRootedTree.defect_nonneg.{uIndex} := @_root_.OAI.RecursivePotentials.FiniteRootedTree.defect_nonneg.{uIndex}
