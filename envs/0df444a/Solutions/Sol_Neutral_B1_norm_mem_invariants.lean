-- Prove2me | solution 1 for Neutral.B1.norm_mem_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:52:10.184002+00:00
-- url     : https://prove2.me/submissions/62feef3a-fa78-4858-a755-4d3eda8946aa

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
theorem _root_.solution [Finite G] (m : M) : normEnd rho m ∈ H0 rho := by
  classical
  letI := Fintype.ofFinite G
  rw [mem_riemannRochSpace_iff_regularAt_everywhere]
  intro g
  rw [normEnd_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => by
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
end Neutral.B1
