-- Prove2me | solution 1 for GlobalTheory.MinorNorm.capelli_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:07:23.371453+00:00
-- url     : https://prove2.me/submissions/426bfe31-1ef8-4ae7-a312-df9e5fe634b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_capelli_step
import Theorems.Thm_GlobalTheory_MinorNorm_cast_eps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)
variable {x d}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0)
    (a : Fin k → ℕ) (P : R) (hup : ∀ i j, i < j → pol x d i j P = 0)
    (hwt : ∀ j, pol x d j j P = a j * P) :
    (Matrix.of x).det * ∑ ρ : Fin k → Fin k, (eps ρ : R) * iterD d k ρ id P =
      ((∏ t, (a t + (k - (t + 1))) : ℕ) : R) * P := by
  have h := capelli_step hd a P hup hwt k id id (fun t => by simp [add_comm])
  have e : (Matrix.of fun t s : Fin k => if id s = id t then (1 : R) else 0) = 1 := by
    ext t s; simp [Matrix.one_apply, eq_comm]
  rw [e, det_one, mul_one] at h
  refine Eq.trans ?_ h
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [cast_eps, ← mul_assoc, mul_comm (Matrix.of x).det, ← det_mul]
  congr 2
  ext t s
  simp [Matrix.mul_apply]
end GlobalTheory.MinorNorm
