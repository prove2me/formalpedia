-- Prove2me | solution 2 for OAI.C0Absorption.diagonal_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:49:05.686377+00:00
-- url     : https://prove2.me/submissions/0fc2eea7-dd0a-4ebb-acdd-668e06022de2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/FiniteShift.lean:L135-L150
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.diagonal_neighborhood. The node keeps its source
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
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Definitions.Def_OAI_Analysis_C0Absorption_Space
import Definitions.Def_OAI_Analysis_C0Absorption_Finite
import Definitions.Def_OAI_Analysis_C0Absorption_FiniteShift

-- ---- from OAI.Analysis.C0Absorption.FiniteShift ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

section FiniteOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end FiniteOperators

theorem diagonal_neighborhood {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup G] (q : X → Y) {x : X} (hq : ContinuousAt q x)
    (A : Y × Y → G) (g : G) (hA : Tendsto A (nhds (q x,q x)) (nhds g))
    {ε : ℝ} (hε : 0<ε) :
    ∃ s : Set X, s∈nhds x ∧ ∀ y∈s, ∀ z∈s, ‖A (q y,q z)-g‖<ε := by
  have hp : Tendsto (fun p : X × X => (q p.1,q p.2)) (nhds (x,x)) (nhds (q x,q x)) :=
    (hq.comp continuous_fst.continuousAt).prodMk (hq.comp continuous_snd.continuousAt)
  have ht := hA.comp hp
  have he : {p : X × X | ‖A (q p.1,q p.2)-g‖<ε}∈nhds (x,x) := by
    have hh := Metric.tendsto_nhds.mp ht ε hε
    change ∀ᶠ p : X × X in nhds (x,x), ‖A (q p.1,q p.2)-g‖<ε
    filter_upwards [hh] with p h
    simpa only [Function.comp_def,dist_eq_norm] using h
  rw [nhds_prod_eq] at he
  obtain ⟨s,hs,t,ht,hst⟩ := Filter.mem_prod_iff.mp he
  exact ⟨s∩t,inter_mem hs ht,fun y hy z hz => @hst (y,z) ⟨hy.1,hz.2⟩⟩

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators


theorem solution : type_of% @_root_.OAI.C0Absorption.diagonal_neighborhood := @_root_.OAI.C0Absorption.diagonal_neighborhood
