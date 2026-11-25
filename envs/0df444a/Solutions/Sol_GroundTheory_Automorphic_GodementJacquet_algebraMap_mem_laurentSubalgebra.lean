-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.algebraMap_mem_laurentSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:52.529873+00:00
-- url     : https://prove2.me/submissions/5a2860df-a697-498e-acda-9f5f7bb289cf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_X_mem_laurentSubalgebra
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_C_mem_laurentSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (P : ℂ[X]) :
    algebraMap ℂ[X] (RatFunc ℂ) P ∈ laurentSubalgebra := by
  refine Polynomial.induction_on P (fun a => ?_) (fun p q hp hq => ?_) (fun k a h => ?_)
  · rw [RatFunc.algebraMap_C]
    exact C_mem_laurentSubalgebra a
  · rw [map_add]
    exact add_mem hp hq
  · rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]
    exact mul_mem h X_mem_laurentSubalgebra
end GroundTheory.Automorphic.GodementJacquet
