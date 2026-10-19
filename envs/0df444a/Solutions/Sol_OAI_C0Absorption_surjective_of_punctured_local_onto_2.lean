-- Prove2me | solution 2 for OAI.C0Absorption.surjective_of_punctured_local_onto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:36:26.973548+00:00
-- url     : https://prove2.me/submissions/b5c4423a-d512-42a8-8c36-2aef6f59bd05

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/LocalInverse.lean:L25-L57
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.surjective_of_punctured_local_onto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators

-- ---- from OAI.Analysis.C0Absorption.LocalInverse ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators

section LocalOnto
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem surjective_of_punctured_local_onto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial E]
    (f : E → F) {c C : ℝ≥0} (hf : AntilipschitzWith c f) (hLip : LipschitzWith C f)
    (hzero : f 0=0) (hconn : IsPreconnected ({0}ᶜ : Set F))
    (hlocal : ∀ x≠0, Set.range f∈nhds (f x)) : Function.Surjective f := by
  let K : Set F := {0}ᶜ
  let A : Set K := Subtype.val ⁻¹' Set.range f
  let : PreconnectedSpace K := Subtype.preconnectedSpace hconn
  have hclosed : IsClosed A := (hf.isClosed_range hLip.uniformContinuous).preimage continuous_subtype_val
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨x,hx⟩ := hy
    have hx0 : x≠0 := by
      intro hx0
      have he : y.val=0 := by rw [← hx,hx0,hzero]
      exact y.property (by simpa only [Set.mem_singleton_iff] using he)
    have hn : Set.range f∈nhds y.val := by rw [← hx]; exact hlocal x hx0
    exact continuous_subtype_val.continuousAt hn
  have hne : A.Nonempty := by
    obtain ⟨x,hx⟩ := exists_ne (0 : E)
    have hx' : f x≠0 := by intro he; exact hx (hf.injective (he.trans hzero.symm))
    refine ⟨⟨f x,?_⟩,x,rfl⟩
    simpa only [K,Set.mem_compl_iff,Set.mem_singleton_iff] using hx'
  have heq : A=Set.univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ hne
  intro y
  by_cases hy : y=0
  · exact ⟨0,hzero.trans hy.symm⟩
  · let yy : K := ⟨y,by simpa only [K,Set.mem_compl_iff,Set.mem_singleton_iff] using hy⟩
    have hh : yy∈A := by rw [heq]; trivial
    exact hh

end LocalOnto
end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators


theorem solution : type_of% @_root_.OAI.C0Absorption.surjective_of_punctured_local_onto := @_root_.OAI.C0Absorption.surjective_of_punctured_local_onto
