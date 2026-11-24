-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:12.080947+00:00
-- url     : https://prove2.me/submissions/b24cacc5-e423-408f-9828-00f2223e86ab

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNeg
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_unop_term
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_qminor_id_rev
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds


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
theorem _root_.solution (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (v : ℂ) :
    MulOpposite.unop (qdet (fun i j => MulOpposite.op (-X i j)) v) =
      ((-1 : ℂ) ^ n) • qdet X ((n : ℂ) - 1 - v) := by
  have hs := quantumMinorColSkew_holds A n n X hX id id (Fin.revPerm : Equiv.Perm (Fin n)) ((n : ℂ) - 1 - v)
  rw [qminor_id_rev] at hs
  have hu : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have h2 := congrArg (fun x => (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) * x) hs
  simp only [← mul_assoc, hu, one_mul] at h2
  have h3 : qdet X ((n : ℂ) - 1 - v) = _ := h2.symm
  rw [h3]
  unfold qdet qminor
  rw [Finset.unop_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun σ _ => unop_term X v σ
end GlobalTheory.CompanionTheory.CapelliAntipode
