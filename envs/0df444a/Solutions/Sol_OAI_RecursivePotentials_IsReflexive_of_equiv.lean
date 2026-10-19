-- Prove2me | solution 1 for OAI.RecursivePotentials.IsReflexive.of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:04:57.226209+00:00
-- url     : https://prove2.me/submissions/fc427138-3569-453c-b281-d493e91df154

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/JoinedGeometry.lean:L186-L202
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.IsReflexive.of_equiv. The node keeps its source
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

lemma IsReflexive.of_equiv {E : Type uSpace} {F : Type uOther} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (hE : IsReflexive E) (e : E ≃L[ℝ] F) :
    IsReflexive F := by
  rw [isReflexive_iff] at hE ⊢
  intro G
  let D : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ F E ℝ).flip e.symm.toContinuousLinearMap
  obtain ⟨x, hx⟩ := hE (G.comp D)
  refine ⟨e x, ?_⟩
  intro f
  have he : D (f.comp e.toContinuousLinearMap) = f := by
    ext y
    change f (e (e.symm y)) = f y
    rw [e.apply_symm_apply]
  have hh := hx (f.comp e.toContinuousLinearMap)
  change G (D (f.comp e.toContinuousLinearMap)) = f (e x) at hh
  rwa [he] at hh

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

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
open OAI OAI.RecursivePotentials
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal


theorem solution.{uSpace,uOther} : type_of% @_root_.OAI.RecursivePotentials.IsReflexive.of_equiv.{uSpace,uOther} := @_root_.OAI.RecursivePotentials.IsReflexive.of_equiv.{uSpace,uOther}
