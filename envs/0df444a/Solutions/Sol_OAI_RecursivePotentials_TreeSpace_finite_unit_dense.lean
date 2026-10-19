-- Prove2me | solution 1 for OAI.RecursivePotentials.TreeSpace.finite_unit_dense
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:36:36.58805+00:00
-- url     : https://prove2.me/submissions/807fa80d-930a-4858-9b07-d42ff8040d2f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean:L1264-L1293
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.TreeSpace.finite_unit_dense. The node keeps its source
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

lemma finite_unit_dense (x : TreeSpace T) (hx : ‖x‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : TreeVector T, ‖v‖ = 1 ∧ ‖(v : TreeSpace T) - x‖ < ε := by
  obtain ⟨v, hv⟩ := Completion.denseRange_coe.exists_dist_lt x
    (lt_min (by positivity : (0 : ℝ) < ε / 4) (by norm_num : (0 : ℝ) < 1 / 2))
  have hvε : ‖(v : TreeSpace T) - x‖ < ε / 4 := by
    simpa only [dist_comm x, dist_eq_norm] using hv.trans_le (min_le_left _ _)
  have hvhalf : ‖(v : TreeSpace T) - x‖ < 1 / 2 := by
    simpa only [dist_comm x, dist_eq_norm] using hv.trans_le (min_le_right _ _)
  have hv0 : v ≠ 0 := by
    intro hv0
    have hvz := congrArg ((↑) : TreeVector T → TreeSpace T) hv0
    rw [Completion.coe_zero] at hvz
    rw [hvz, zero_sub, norm_neg, hx] at hvhalf
    norm_num at hvhalf
  let w : TreeVector T := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv0
  have hscale : ‖v‖ • w = v := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
  have hsub : ‖w - v‖ = |1 - ‖v‖| := by
    have he : w - v = (1 - ‖v‖) • w := by rw [sub_smul, one_smul, hscale]
    rw [he, norm_smul, Real.norm_eq_abs, hw, mul_one]
  have hreverse := abs_norm_sub_norm_le (v : TreeSpace T) x
  rw [Completion.norm_coe, hx, abs_sub_comm] at hreverse
  have hdist : ‖(w : TreeSpace T) - (v : TreeSpace T)‖ ≤ ‖(v : TreeSpace T) - x‖ := by
    rw [← Completion.coe_sub, Completion.norm_coe, hsub]
    exact hreverse
  refine ⟨w, hw, ?_⟩
  have htri := norm_sub_le_norm_sub_add_norm_sub (w : TreeSpace T) (v : TreeSpace T) x
  exact htri.trans_lt (by linarith)

end TreeSpace

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
open scoped BigOperators
open UniformSpace


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.TreeSpace.finite_unit_dense.{uIndex} := @_root_.OAI.RecursivePotentials.TreeSpace.finite_unit_dense.{uIndex}
