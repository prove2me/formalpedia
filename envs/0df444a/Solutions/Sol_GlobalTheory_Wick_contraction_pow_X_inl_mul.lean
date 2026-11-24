-- Prove2me | solution 1 for GlobalTheory.Wick.contraction_pow_X_inl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:08.840652+00:00
-- url     : https://prove2.me/submissions/74ac4ea3-84ec-4465-ae3f-073f8291cd8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Theorems.Thm_GlobalTheory_Wick_commute_contraction_rowContraction
import Theorems.Thm_GlobalTheory_Wick_contraction_X_inl_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}
variable [Fintype κ]
variable [Fintype ι]
namespace GlobalTheory.Wick
theorem _root_.solution (γ : ι → κ → R) (n : ℕ) (i : ι) (P : MvPolynomial (ι ⊕ κ) R) :
    (contraction γ ^ (n + 1)) (X (Sum.inl i) * P) =
      X (Sum.inl i) * (contraction γ ^ (n + 1)) P +
        (n + 1) • rowContraction γ i ((contraction γ ^ n) P) := by
  induction n with
  | zero => simp [contraction_X_inl_mul]
  | succ n ih =>
    have hc (Q) : contraction γ (rowContraction γ i Q) = rowContraction γ i (contraction γ Q) :=
      LinearMap.congr_fun (commute_contraction_rowContraction γ i).eq Q
    rw [pow_succ' _ (n + 1), Module.End.mul_apply, ih, map_add, contraction_X_inl_mul, map_nsmul,
      hc, Module.End.mul_apply, ← Module.End.mul_apply (contraction γ) (contraction γ ^ n),
      ← pow_succ', succ_nsmul' _ (n + 1), add_assoc]
end GlobalTheory.Wick
