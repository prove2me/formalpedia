-- Prove2me | solution 1 for OAI.RecursivePotentials.TreeSpace.averaged_modulus_cubic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:38:02.243859+00:00
-- url     : https://prove2.me/submissions/1e043baa-584c-4620-adc6-7383d99a1c03

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean:L1295-L1319
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.TreeSpace.averaged_modulus_cubic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Theorems.Thm_OAI_RecursivePotentials_TreeSpace_finite_center_midpoint_gap
import Theorems.Thm_OAI_RecursivePotentials_TreeSpace_finite_unit_dense
import Theorems.Thm_OAI_RecursivePotentials_averagedModulus_lower_of_witness

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

lemma not_finite_dimensional {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) [Infinite ι] :
    ¬Module.Finite ℝ (TreeVector T) := by
  intro h
  let : Module.Finite ℝ (ι →₀ ℝ) := h
  exact Infinite.not_finite (Module.Finite.finite_basis (Finsupp.basisSingleOne : Module.Basis ι ℝ (ι →₀ ℝ)))

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (TreeSpace T) := by
  intro h
  let := h
  have hf := FiniteDimensional.of_injective
    (Completion.toComplL : TreeVector T →L[ℝ] TreeSpace T).toLinearMap
    (Completion.coe_injective (TreeVector T))
  exact TreeVector.not_finite_dimensional T hf

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

theorem averaged_modulus_cubic [Infinite ι] {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t ^ 3 / 128 ≤ averagedModulus (TreeSpace T) t := by
  apply averagedModulus_lower_of_witness (not_finite_dimensional T) ht.le
  intro x hx ε hε
  obtain ⟨v, hv, hvx⟩ := finite_unit_dense T x hx hε
  let H := T.head (show ι →₀ ℝ from v)
  have hH : T.Initial H := T.head_initial v
  refine ⟨cofiniteTail T H hH, ?_⟩
  intro y hy hy1
  have hty : t ≤ ‖t • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hzy : t • y ∈ tail T H hH := (tail T H hH).smul_mem t hy
  have hfinite := finite_center_midpoint_gap T v hH (T.support_subset_head v) hv
    (t • y) hzy ht ht1 hty
  have h₁ : ‖(v : TreeSpace T) + t • y‖ ≤ ‖x + t • y‖ + ‖(v : TreeSpace T) - x‖ := by
    calc
      ‖(v : TreeSpace T) + t • y‖ = ‖x + t • y + ((v : TreeSpace T) - x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have h₂ : ‖(v : TreeSpace T) - t • y‖ ≤ ‖x - t • y‖ + ‖(v : TreeSpace T) - x‖ := by
    calc
      ‖(v : TreeSpace T) - t • y‖ = ‖x - t • y + ((v : TreeSpace T) - x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  unfold averagedGain
  linarith

end TreeSpace

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
open scoped BigOperators
open UniformSpace


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.TreeSpace.averaged_modulus_cubic.{uIndex} := @_root_.OAI.RecursivePotentials.TreeSpace.averaged_modulus_cubic.{uIndex}
