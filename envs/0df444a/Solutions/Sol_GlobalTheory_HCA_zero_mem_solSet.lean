-- Prove2me | solution 1 for GlobalTheory.HCA.zero_mem_solSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:27.7768+00:00
-- url     : https://prove2.me/submissions/61d4610a-cdc0-44cd-8edf-519eac62577d

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllReg
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ZetaZeros.D.EllReg
open scoped BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
variable {d : ℕ}
open scoped BoundedContinuousFunction
variable {d : ℕ}
namespace GlobalTheory.HCA
namespace _root_.GlobalTheory.HCA
theorem _root_.solution {ι : Type} (P : _root_.ZetaZeros.D.EllReg.Sys d ι) (U : Set (_root_.ZetaZeros.D.EllReg.E d)) :
    (0 : U →ᵇ ℂ) ∈ _root_.GlobalTheory.HCA.solSet P U := by
  have h : _root_.GlobalTheory.HCA.ext0 U (0 : U →ᵇ ℂ) = fun _ => 0 := by
    funext x
    unfold _root_.GlobalTheory.HCA.ext0
    split_ifs <;> rfl
  show _root_.ZetaZeros.D.EllReg.WeakSol P U (_root_.GlobalTheory.HCA.ext0 U (0 : U →ᵇ ℂ))
  rw [h]
  unfold _root_.ZetaZeros.D.EllReg.WeakSol
  intro i φ _ _ _
  simp
end _root_.GlobalTheory.HCA
end GlobalTheory.HCA
