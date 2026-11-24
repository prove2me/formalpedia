-- Prove2me | solution 1 for GlobalTheory.pic_pi_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:12.147316+00:00
-- url     : https://prove2.me/submissions/b31cc531-bd7d-4fa1-b6d7-b103a1d16863

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrder
import Theorems.Thm_GlobalTheory_PicPi_eq_one_of_forall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)],
    (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) →
      ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by
  intro ι _ R _ hR M
  classical
  haveI := Fintype.ofFinite ι
  have hk : 0 < ∏ i, orderOf (CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M) :=
    Finset.prod_pos fun i _ => (hR i _).orderOf_pos
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hk, ?_⟩
  apply PicPi.eq_one_of_forall
  intro i
  rw [map_pow]
  exact orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
end GlobalTheory
