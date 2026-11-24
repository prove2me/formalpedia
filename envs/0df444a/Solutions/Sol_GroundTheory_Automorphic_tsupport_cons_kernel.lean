-- Prove2me | solution 1 for GroundTheory.Automorphic.tsupport_cons_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:12.614318+00:00
-- url     : https://prove2.me/submissions/88044085-287c-4cd7-9bd9-233e58bbe3bb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ}
    (has : tsupport a ⊆ Icc (-ε) ε)
    (hKs : tsupport K ⊆ Metric.closedBall 0 ε) :
    tsupport (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) ⊆ Metric.closedBall 0 ε := by
  intro t ht
  have h1 := tsupport_mul_subset_left ht
  have h2 := tsupport_mul_subset_right ht
  have h1' : t 0 ∈ tsupport a :=
    tsupport_comp_subset_preimage a (f := fun t : Fin (d + 1) → ℝ => t 0) (continuous_apply 0) h1
  have h2' : Fin.tail t ∈ tsupport K :=
    tsupport_comp_subset_preimage K (f := fun t : Fin (d + 1) → ℝ => Fin.tail t)
      (continuous_pi fun j => continuous_apply j.succ) h2
  have ha' := has h1'
  have hK' := hKs h2'
  rw [mem_closedBall_zero_iff] at hK' ⊢
  refine (pi_norm_le_iff_of_nonneg hε).2 fun j => ?_
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [Real.norm_eq_abs, abs_le]; exact ha'
  · exact (norm_le_pi_norm (Fin.tail t) j).trans hK'
end GroundTheory.Automorphic
