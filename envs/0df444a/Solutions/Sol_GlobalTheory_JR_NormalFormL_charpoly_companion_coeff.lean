-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.charpoly_companion_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:00:42.401674+00:00
-- url     : https://prove2.me/submissions/a1c70422-db3c-4114-8517-f2c8dc2b81aa

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_sum_mulVec__fc8d7b839a0b
import Theorems.Thm_GlobalTheory_JR_NormalFormL_pow_card_eq
import Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_pow_ev
import Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_pow_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (p : Fin r → k) (i : Fin r) :
    (companion p).charpoly.coeff i = p i := by
  have hr : 0 < r := i.pos
  have h := pow_card_eq (companion p)
  have h2 := congrArg (fun M => M *ᵥ ev r k 0) h
  simp only [companion_pow_card p hr, neg_mulVec, sum_mulVec', smul_mulVec] at h2
  have h3 := congrFun h2 i
  simp only [Pi.neg_apply, neg_inj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  rw [h3, Finset.sum_eq_single (i : ℕ)]
  · simp [companion_pow_ev p i i.2, ev]
  · intro b hb hne
    rw [companion_pow_ev p b (Finset.mem_range.mp hb)]
    simp [ev, Ne.symm hne]
  · intro h; exact absurd (Finset.mem_range.mpr i.2) h
end GlobalTheory.JR.NormalFormL
