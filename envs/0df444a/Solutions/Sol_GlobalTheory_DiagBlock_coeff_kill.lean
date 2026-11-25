-- Prove2me | solution 1 for GlobalTheory.DiagBlock.coeff_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:17.387199+00:00
-- url     : https://prove2.me/submissions/f3d17c3c-cad6-41a0-b96c-c9f3af3a173a

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_kill_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
variable {R : Type} [CommRing R] {σ : Type}
open Classical
namespace GlobalTheory.DiagBlock
theorem _root_.solution (S : σ → Prop) [DecidablePred S] (P : MvPolynomial σ R) (e : σ →₀ ℕ) :
    MvPolynomial.coeff e (kill S P) =
      if ∀ x, S x → e x = 0 then MvPolynomial.coeff e P else 0 := by
  refine MvPolynomial.induction_on' P (fun m c => ?_) (fun p q hp hq => ?_)
  · rw [kill_monomial]
    by_cases hme : m = e
    · subst hme
      split_ifs <;> simp
    · split_ifs <;> simp [MvPolynomial.coeff_monomial, hme]
  · rw [map_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
    split_ifs <;> simp
end GlobalTheory.DiagBlock
