-- Prove2me | solution 1 for GlobalTheory.SymmTensor.sum_tens_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:41.081506+00:00
-- url     : https://prove2.me/submissions/f8afd33b-ba56-4500-ab08-c8087f6a80e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPerm
import Theorems.Thm_GlobalTheory_SymmTensor_tens_single_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SymmTensor
variable {n d : ℕ}
namespace GlobalTheory.SymmTensor
theorem _root_.solution (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ a, ∑ b, Y a b • polar n d a b := by
  ext I K
  simp only [Matrix.sum_apply, tens_single_apply, polar, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    Finset.mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : ∀ q, q ≠ p → I q = K q
  · simp [eq_true h, ite_and]
  · simp [eq_false h]
end GlobalTheory.SymmTensor
