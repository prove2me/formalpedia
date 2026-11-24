-- Prove2me | solution 1 for GlobalTheory.WeylDuality.applyWord_mem_dualWeyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:46.884311+00:00
-- url     : https://prove2.me/submissions/d942ad75-06ec-4adc-8673-bfa65fb94d58

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (ν : Fin n → ℕ)
    (w : List (Fin r × Fin r × ℕ)) {F : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) :
    applyWord R w F ∈ dualWeyl R r n ν := by
  induction w with
  | nil => simpa [applyWord] using hF
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih
end GlobalTheory.WeylDuality
