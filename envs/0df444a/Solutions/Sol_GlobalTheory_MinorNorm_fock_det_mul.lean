-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_det_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:43:06.919808+00:00
-- url     : https://prove2.me/submissions/8077d8f0-2b29-4b92-9465-7c0400c752a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_det_eq_sum_eps
import Theorems.Thm_GlobalTheory_MinorNorm_capelli_hw
import Theorems.Thm_GlobalTheory_MinorNorm_fock_sum_left
import Theorems.Thm_GlobalTheory_MinorNorm_fock_sum_right
import Theorems.Thm_GlobalTheory_MinorNorm_fock_int_left
import Theorems.Thm_GlobalTheory_MinorNorm_fock_int_right
import Theorems.Thm_GlobalTheory_MinorNorm_fock_prod_mul

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
variable {σ : Type}
namespace GlobalTheory.MinorNorm
theorem _root_.solution {k : ℕ} (v : Fin k → Fin k → σ)
    (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) (a : Fin k → ℕ) (P' P : MvPolynomial σ ℂ)
    (hP : P = (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)).det * P')
    (hdet : (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)).det ≠ 0)
    (hup : ∀ i j, i < j → pol (fun r c => X (v r c)) (fun r c => pderiv (v r c)) i j P = 0)
    (hwt : ∀ j, pol (fun r c => X (v r c)) (fun r c => pderiv (v r c)) j j P = a j * P) :
    Formalism.E.fock P P = ((∏ t, (a t + (k - (t + 1))) : ℕ) : ℂ) * Formalism.E.fock P' P' := by
  classical
  have hd : ∀ r j s c, pderiv (v r j) (X (v s c) : MvPolynomial σ ℂ) =
      if r = s ∧ j = c then 1 else 0 := by
    intro r j s c
    split_ifs with h
    · rw [h.1, h.2, pderiv_X_self]
    · exact pderiv_X_of_ne fun h' => h (hv _ _ _ _ h'.symm)
  have h := capelli_hw (x := fun r c => X (v r c)) (d := fun r c => pderiv (v r c)) hd a P hup hwt
  have h2 : ∑ ρ : Fin k → Fin k, (eps ρ : MvPolynomial σ ℂ) *
      iterD (fun r c => pderiv (v r c)) k ρ id P =
      (((∏ t, (a t + (k - (t + 1))) : ℕ) : ℤ) : MvPolynomial σ ℂ) * P' := by
    apply mul_left_cancel₀ hdet
    rw [h, Int.cast_natCast]
    conv_lhs => rw [hP]
    ring
  have h3 : Formalism.E.fock P P = Formalism.E.fock P' (∑ ρ : Fin k → Fin k, (eps ρ : MvPolynomial σ ℂ) *
      iterD (fun r c => pderiv (v r c)) k ρ id P) := by
    conv_lhs => enter [1]; rw [hP, det_eq_sum_eps, Finset.sum_mul]
    rw [fock_sum_left, fock_sum_right]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [mul_assoc, fock_int_left, fock_int_right, ← fock_prod_mul]
    rfl
  rw [h3, h2, fock_int_right, Int.cast_natCast]
end GlobalTheory.MinorNorm
