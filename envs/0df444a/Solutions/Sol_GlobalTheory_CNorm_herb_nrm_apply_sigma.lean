-- Prove2me | solution 1 for GlobalTheory.CNorm.herb_nrm_apply_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:06:54.696287+00:00
-- url     : https://prove2.me/submissions/416a03dd-146b-4031-bac0-200459dd5f49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormDifferenceIndexIdentity
import Theorems.Thm_GlobalTheory_CNorm_nrm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution {A : Type} [CommGroup A] (σ : A →* A) (p : ℕ)
    (h : ∀ a, σ^[p] a = a) (a : A) : nrm σ p (σ a) = nrm σ p a := by
  have e1 := Finset.prod_range_succ (fun i => σ^[i] a) p
  have e2 := Finset.prod_range_succ' (fun i => σ^[i] a) p
  rw [e1] at e2
  simp only [h, Function.iterate_zero, id, Function.iterate_succ_apply] at e2
  rw [nrm_apply, nrm_apply]
  exact (mul_right_cancel e2).symm
end GlobalTheory.CNorm
