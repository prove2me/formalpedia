-- Prove2me | solution 1 for OAI.RecursivePotentials.hilbert_isReflexive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:06:27.839866+00:00
-- url     : https://prove2.me/submissions/4be5e230-823f-4380-9d99-d49a02bf55df

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/JoinedGeometry.lean:L204-L220
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.hilbert_isReflexive. The node keeps its source
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

lemma hilbert_isReflexive {E : Type uSpace} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : IsReflexive E := by
  rw [isReflexive_iff]
  intro F
  let d := InnerProductSpace.toDual ℝ E
  let g : E →L[ℝ] ℝ := F.comp d.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨d.symm g, ?_⟩
  intro f
  have he : d (d.symm f) = f := d.apply_symm_apply f
  have hg : d (d.symm g) = g := d.apply_symm_apply g
  have h := congrArg (fun k : E →L[ℝ] ℝ => k (d.symm f)) hg
  change inner ℝ (d.symm g) (d.symm f) = F (d (d.symm f)) at h
  rw [he] at h
  have h' := congrArg (fun k : E →L[ℝ] ℝ => k (d.symm g)) he
  change inner ℝ (d.symm f) (d.symm g) = f (d.symm g) at h'
  rw [real_inner_comm] at h'
  exact h.symm.trans h'

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


theorem solution.{uSpace} : type_of% @_root_.OAI.RecursivePotentials.hilbert_isReflexive.{uSpace} := @_root_.OAI.RecursivePotentials.hilbert_isReflexive.{uSpace}
