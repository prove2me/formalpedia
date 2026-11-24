-- Prove2me | solution 1 for GlobalTheory.DetClass.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:11:02.042588+00:00
-- url     : https://prove2.me/submissions/b7df882a-7fb5-4656-a928-fcbe3ac981a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.DetClass
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.DetClass
theorem _root_.solution {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (a : (i : ι) → I i) : (mat φ a).det ∈ ∏ j, J j := by
  rw [Matrix.det_apply]
  refine Ideal.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  have h : ∏ i, (mat φ a) (σ i) i ∈ ∏ i, J (σ i) :=
    Ideal.prod_mem_prod fun i _ => (φ (Pi.single i (a i)) (σ i)).2
  rwa [Equiv.prod_comp σ J] at h
end GlobalTheory.DetClass
