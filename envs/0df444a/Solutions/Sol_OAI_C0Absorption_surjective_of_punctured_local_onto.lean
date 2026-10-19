-- Prove2me | solution 1 for OAI.C0Absorption.surjective_of_punctured_local_onto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:37:41.803978+00:00
-- url     : https://prove2.me/submissions/d2d63710-6326-4e3f-ba2d-336350d46a1c

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial E]
    (f : E → F) {c C : ℝ≥0} (hf : AntilipschitzWith c f) (hLip : LipschitzWith C f)
    (hzero : f 0=0) (hconn : IsPreconnected ({0}ᶜ : Set F))
    (hlocal : ∀ x≠0, Set.range f∈nhds (f x)) : Function.Surjective f := by
  have hinj : Function.Injective f := hf.injective
  have hcl : IsClosed (Set.range f) := hf.isClosed_range hLip.uniformContinuous
  set u : Set F := interior (Set.range f) ∩ {0}ᶜ
  have hu : IsOpen u := isOpen_interior.inter isOpen_compl_singleton
  have hne0 : ∀ x, x ≠ 0 → f x ≠ 0 := fun x hx h => hx (hinj (h.trans hzero.symm))
  have hmem : ∀ x, x ≠ 0 → f x ∈ u := fun x hx =>
    ⟨mem_interior_iff_mem_nhds.2 (hlocal x hx), hne0 x hx⟩
  obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
  have hsub : ({0}ᶜ : Set F) ⊆ u := by
    refine hconn.subset_of_closure_inter_subset hu ⟨f x0, hne0 x0 hx0, hmem x0 hx0⟩ ?_
    rintro y ⟨hy, hy0⟩
    have : y ∈ Set.range f := hcl.closure_subset (closure_mono (fun z hz => interior_subset hz.1) hy)
    obtain ⟨x, rfl⟩ := this
    have hx : x ≠ 0 := by rintro rfl; exact hy0 hzero
    exact hmem x hx
  intro y
  by_cases hy : y = 0
  · exact ⟨0, hy ▸ hzero⟩
  · exact (interior_subset (s := Set.range f) (hsub hy).1 : y ∈ Set.range f)

