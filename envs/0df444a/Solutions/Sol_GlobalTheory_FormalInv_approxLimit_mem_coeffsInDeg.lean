-- Prove2me | solution 1 for GlobalTheory.FormalInv.approxLimit_mem_coeffsInDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:47:12.835802+00:00
-- url     : https://prove2.me/submissions/dc28849d-9939-45e4-9b71-9ab56643f3b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_smul_mem_coeffsIn
import Theorems.Thm_GlobalTheory_FormalInv_X_mem_coeffsIn
import Theorems.Thm_GlobalTheory_FormalInv_subst_mem_coeffsInDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable [Fintype σ] [Fintype τ] (u : σ → MvPowerSeries τ R) (B : Matrix τ σ R)
variable {u} {B}
namespace GlobalTheory.FormalInv
theorem _root_.solution (hu : ∀ i, constantCoeff (u i) = 0) {S : Subring R} {g : ℕ}
    (hB : ∀ j i, B j i ∈ S) (huS : ∀ i, higherPart u i ∈ coeffsInDeg τ S g) (j : τ) :
    approxLimit u B j ∈ coeffsInDeg σ S g := by
  have : ∀ n j, ((approxStep u B)^[n] 0) j ∈ coeffsInDeg σ S g := by
    intro n
    induction n with
    | zero => intro j; exact Subring.zero_mem _
    | succ n ih =>
      intro j
      rw [Function.iterate_succ_apply']
      exact Subring.sum_mem _ fun i _ => smul_mem_coeffsIn (hB j i) (Subring.sub_mem _
        (X_mem_coeffsIn i) (subst_mem_coeffsInDeg
          (fun s => mem_degGe_one.1 (iterate_mem_degGe hu n s)) ih (huS i)))
  intro d hd
  exact this _ j d hd
end GlobalTheory.FormalInv
