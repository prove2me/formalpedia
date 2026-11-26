-- Prove2me | solution 1 for GlobalTheory.eq_zero_or_totallyPos
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:32:07.812777+00:00
-- url     : https://prove2.me/submissions/18425a2a-eaac-403c-a756-a2663e7150b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
theorem _root_.solution {a : F} (ha : ∀ σ : F →+* ℝ, 0 ≤ σ a) :
    a = 0 ∨ ∀ σ : F →+* ℝ, 0 < σ a := by
  first
    | (by_cases h : a = 0
       · exact Or.inl h
       · refine Or.inr fun σ => lt_of_le_of_ne (ha σ) (fun h0 => h ?_)
         exact (map_eq_zero σ).1 h0.symm)

