-- Prove2me | solution 1 for GlobalTheory.exists_biadditive_of_secondDiff_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:51.642882+00:00
-- url     : https://prove2.me/submissions/c6dcc84f-5378-4fb7-9347-e77e97c2babb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_HasConstSecondDiff_bilin_apply
import Theorems.Thm_GlobalTheory_HasConstSecondDiff_bilin_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]
namespace GlobalTheory
theorem _root_.solution (f : X → A)
    (h : ∀ a a' μ ν : X, f (a + μ + ν) - f (a + μ) - f (a + ν) + f a =
      f (a' + μ + ν) - f (a' + μ) - f (a' + ν) + f a') :
    ∃ B : X →+ X →+ A, (∀ a μ ν, B μ ν = f (a + μ + ν) - f (a + μ) - f (a + ν) + f a) ∧
      ∀ μ ν, B μ ν = B ν μ := by
  have h' : HasConstSecondDiff f := h
  exact ⟨LinearMap.toAddMonoidHom'.comp h'.bilin.toAddMonoidHom, h'.bilin_apply, h'.bilin_comm⟩
end GlobalTheory
