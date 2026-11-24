-- Prove2me | solution 1 for GlobalTheory.PMonE.gsum_lowerOrder_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:18:38.554698+00:00
-- url     : https://prove2.me/submissions/ae577fa6-88a5-4fd7-a044-5943c9ac331f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
namespace GlobalTheory.PMonE
theorem _root_.solution (q : ℕ) (N D : ℕ) (M : ℕ → Matrix m m F) (z : m ⊕ m → F)
    (hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ q) (i : m) :
    gsum q D (lowerOrder N M) z (Sum.inr i) = gsum q (D + 1) M (fun j => z (Sum.inl j)) i := by

  have h : ∀ n, (lowerOrder N M n).mulVec (fun k => z k ^ q ^ n) (Sum.inr i) =
      (if n = 0 then (M 0).mulVec (fun j => z (Sum.inl j) ^ q ^ 0) i else 0) +
        (M (n + 1)).mulVec (fun j => z (Sum.inl j) ^ q ^ (n + 1)) i := by
    intro n
    simp only [lowerOrder, Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, Function.comp_def, hz]
    congr 1
    · split_ifs with h0
      · subst h0
        rfl
      · simp
    · congr 2
      funext j
      rw [← pow_mul, ← pow_succ']
  simp only [gsum, Finset.sum_apply, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [Finset.sum_range_succ' _ (D + 1), if_pos (by omega), add_comm]
end GlobalTheory.PMonE
