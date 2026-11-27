-- Prove2me | solution 2 for Neutral.B1.normSub_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:52:06.662524+00:00
-- url     : https://prove2.me/submissions/c32fba52-8d21-4219-956d-a3b843dd3186

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Theorems.Thm_Neutral_B1_normEnd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
namespace Neutral.B1
theorem _root_.solution [Finite G] [Subsingleton G] : normSub rho = ⊤ := by
  classical
  letI := Fintype.ofFinite G
  refine eq_top_iff.2 fun x _ => Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨x.1, ?_⟩)
  rw [normEnd_apply, Fintype.sum_subsingleton _ 1, map_one, Module.End.one_apply]
  rfl
end Neutral.B1
