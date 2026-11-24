-- Prove2me | solution 1 for GlobalTheory.DI.delta_delta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:13.032905+00:00
-- url     : https://prove2.me/submissions/c1b545ea-bc01-471b-aee6-efebf4088ecd

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
namespace GlobalTheory.DI
theorem _root_.solution (c : Finset ι → E) : delta (delta c) = 0 := by
  funext t
  let f : ι × ι → E := fun q =>
    (cubeSign t q.1 * cubeSign (t.erase q.1) q.2) • c ((t.erase q.1).erase q.2)
  have h1 : delta (delta c) t = ∑ q ∈ t.offDiag, f q := by
    show ∑ i ∈ t, cubeSign t i • delta c (t.erase i) = _
    rw [Finset.sum_finset_product t.offDiag t (fun i => t.erase i)
      (fun q => by simp only [Finset.mem_offDiag, Finset.mem_erase]; tauto)]
    refine Finset.sum_congr rfl fun i _ => ?_
    show cubeSign t i • ∑ j ∈ t.erase i, cubeSign (t.erase i) j • c ((t.erase i).erase j) = _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [f, smul_smul]
  rw [h1, Pi.zero_apply]
  refine Finset.sum_involution (fun q _ => q.swap) (fun q hq => ?_) (fun q hq _ h => ?_)
    (fun q hq => ?_) (fun q _ => rfl)
  · rw [Finset.mem_offDiag] at hq
    simp only [f, Prod.fst_swap, Prod.snd_swap]
    rw [cubeSign_mul_erase hq.1 hq.2.1 hq.2.2, Finset.erase_right_comm (a := q.1) (b := q.2),
      neg_smul, neg_add_cancel]
  · rw [Finset.mem_offDiag] at hq
    exact hq.2.2 (congrArg Prod.snd h)
  · rw [Finset.mem_offDiag] at hq ⊢
    exact ⟨hq.2.1, hq.1, hq.2.2.symm⟩
end GlobalTheory.DI
