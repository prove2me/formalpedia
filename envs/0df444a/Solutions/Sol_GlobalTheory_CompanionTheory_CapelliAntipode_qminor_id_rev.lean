-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAntipode.qminor_id_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:40.999705+00:00
-- url     : https://prove2.me/submissions/03470c25-224c-4fbd-92eb-56c580e177a7

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAntipode
namespace GlobalTheory.CompanionTheory.CapelliAntipode
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ) :
    qminor X id (id ∘ (Fin.revPerm : Equiv.Perm (Fin n))) w =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
        ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
          (List.ofFn fun j : Fin n => Tm X (w - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod := by
  unfold qminor
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ (fun σ => ?_)).symm
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Equiv.Perm.mul_apply, Fin.revPerm_apply,
    Function.comp_apply, id, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, Int.cast_comm]
end GlobalTheory.CompanionTheory.CapelliAntipode
