-- Prove2me | solution 1 for Neutral.B1.normEnd_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:29.074519+00:00
-- url     : https://prove2.me/submissions/28d35fd5-cb63-4d41-9356-420d7ab5e2c9

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
namespace Neutral.B1
theorem _root_.solution [Finite G] [Fintype G] (m : M) : normEnd rho m = ∑ g : G, rho g m := by
  rw [normEnd, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
end Neutral.B1
