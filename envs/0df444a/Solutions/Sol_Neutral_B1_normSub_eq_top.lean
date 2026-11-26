-- Prove2me | solution 1 for Neutral.B1.normSub_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:50:24.92207+00:00
-- url     : https://prove2.me/submissions/a121718c-addb-4ea6-ab69-af01d94fdece

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
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
theorem _root_.solution [Finite G] [Subsingleton G] : normSub rho = ⊤ := by
  unfold Neutral.B1.normSub
  rw [eq_top_iff]
  intro x _
  have : Unique G := uniqueOfSubsingleton 1
  show (x : M) ∈ LinearMap.range (Neutral.B1.normEnd rho)
  refine ⟨(x : M), ?_⟩
  unfold Neutral.B1.normEnd
  rw [finsum_unique, Subsingleton.elim (default : G) 1, map_one]
  rfl

