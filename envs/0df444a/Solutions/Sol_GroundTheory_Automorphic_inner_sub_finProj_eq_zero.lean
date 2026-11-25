-- Prove2me | solution 1 for GroundTheory.Automorphic.inner_sub_finProj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:52.606459+00:00
-- url     : https://prove2.me/submissions/2bf68223-995c-4f2f-aab4-8dc0421ff84a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Theorems.Thm_GroundTheory_Automorphic_inner_finProj_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι]
variable {u : ι → H}
namespace GroundTheory.Automorphic
theorem _root_.solution (hu : Orthonormal ℂ u) (x : H) {g : H}
    (hg : g ∈ Submodule.span ℂ (Set.range u)) : ⟪g, x - finProj u x⟫_ℂ = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hg
  rw [sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_smul_left, inner_sub_right, inner_finProj_right hu, sub_self, mul_zero]
end GroundTheory.Automorphic
