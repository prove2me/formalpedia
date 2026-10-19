-- Prove2me | solution 1 for OAI.RecursivePotentials.SquareSum.isReflexive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:07:58.460426+00:00
-- url     : https://prove2.me/submissions/ff340cd0-91d9-4c54-9e95-815aba1f26d3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/JoinedGeometry.lean:L338-L363
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.SquareSum.isReflexive. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry

-- ---- from OAI.Analysis.RecursivePotentials.JoinedGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end FiniteRootedTree

open Filter Topology

open scoped ENNReal

noncomputable section

lemma isReflexive_iff {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsReflexive E ↔ ∀ F : (E →L[ℝ] ℝ) →L[ℝ] ℝ, ∃ x : E, ∀ f : E →L[ℝ] ℝ, F f = f x := by
  constructor
  · intro h F
    obtain ⟨x, hx⟩ := h F
    exact ⟨x, fun f => (congrArg (fun G : (E →L[ℝ] ℝ) →L[ℝ] ℝ => G f) hx).symm⟩
  · intro h F
    obtain ⟨x, hx⟩ := h F
    exact ⟨x, ContinuousLinearMap.ext (fun f => (hx f).symm)⟩

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

theorem isReflexive (hE : ∀ i, IsReflexive (E i)) : IsReflexive (Space E) := by
  rw [isReflexive_iff]
  intro F
  let G : Space (DualFamily E) →L[ℝ] ℝ := F.comp (pairing E)
  let r := restrict (DualFamily E) G
  choose x hx using fun i => hE i (r i)
  have hnorm : ∀ i, ‖x i‖ = ‖r i‖ := by
    intro i
    rw [← (NormedSpace.inclusionInDoubleDualLi (E := E i) ℝ).norm_map]
    exact congrArg norm (hx i)
  have hmem : Memℓp x 2 := by
    apply memℓp_norm_iff.mp
    simpa only [hnorm] using (lp.memℓp r).norm
  let v : Space E := ⟨x, hmem⟩
  have hG : G = (pairing E).flip v := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro i
    ext f
    change (r i) f = pairing E (lp.single 2 i f) v
    rw [pairing_single_left]
    exact (congrArg (fun H : (E i →L[ℝ] ℝ) →L[ℝ] ℝ => H f) (hx i)).symm
  refine ⟨v, ?_⟩
  intro f
  have hh := congrArg (fun H : Space (DualFamily E) →L[ℝ] ℝ => H (restrict E f)) hG
  change F (pairing E (restrict E f)) = pairing E (restrict E f) v at hh
  simpa only [pairing_restrict] using hh

end SquareSum

end

open UniformSpace

noncomputable section

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

end SquareSum

end

namespace TreeVector

open scoped ENNReal

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeVector

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeSpace

namespace Joined

noncomputable section

open UniformSpace

end

end Joined

namespace Joined

noncomputable section

open UniformSpace

end

end Joined

noncomputable section

end

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeSpace

open Filter

open scoped Topology

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeSpace

section Lens

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Lens

namespace TreeSpace

noncomputable section

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeSpace

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.SquareSum
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal


theorem solution.{uIndex,uFiber} : type_of% @_root_.OAI.RecursivePotentials.SquareSum.isReflexive.{uIndex,uFiber} := @_root_.OAI.RecursivePotentials.SquareSum.isReflexive.{uIndex,uFiber}
