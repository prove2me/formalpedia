-- Prove2me | solution 1 for GlobalTheory.TupleCone.piece_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:05.663191+00:00
-- url     : https://prove2.me/submissions/9fde03f4-c6c6-4184-8574-a97e1702ba87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
import Theorems.Thm_GlobalTheory_TupleCone_mem_piece
import Theorems.Thm_GlobalTheory_TupleCone_coeff_mem_span_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}
namespace GlobalTheory.TupleCone
theorem _root_.solution : piece o t 0 = (integralClosure o L).toSubmodule := by
  ext a
  rw [mem_piece, pow_zero, mul_one, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
  constructor
  · intro h
    have h1 : ∀ s : cone o t, ((evalRingHom 0).comp (algebraMap (cone o t) L[X])) s ∈
        (⊥ : Subalgebra o L) := fun s => by
      have := coeff_mem_span_pow s.2 0
      rw [pow_zero, Submodule.mem_one, coeff_zero_eq_eval_zero] at this
      exact Algebra.mem_bot.mpr this
    have h2 : IsIntegral (⊥ : Subalgebra o L) (evalRingHom 0 (C a)) :=
      h.map_of_comp_eq (RingHom.codRestrict _ _ h1) (evalRingHom 0) rfl
    rw [coe_evalRingHom, eval_C] at h2
    haveI : Algebra.IsIntegral o (⊥ : Subalgebra o L) := inferInstance
    exact isIntegral_trans a h2
  · intro h
    exact (h.map (CAlgHom (R := o) (A := L))).tower_top
end GlobalTheory.TupleCone
