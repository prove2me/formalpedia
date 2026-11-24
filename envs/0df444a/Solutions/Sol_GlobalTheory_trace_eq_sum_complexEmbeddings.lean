-- Prove2me | solution 1 for GlobalTheory.trace_eq_sum_complexEmbeddings
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:23.341803+00:00
-- url     : https://prove2.me/submissions/ec1a767a-0655-4970-be63-b920e0a8e5ff

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
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ x := by
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)]
  simp
end GlobalTheory
