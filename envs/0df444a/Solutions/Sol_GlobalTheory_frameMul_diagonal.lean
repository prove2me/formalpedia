-- Prove2me | solution 1 for GlobalTheory.frameMul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:02.30283+00:00
-- url     : https://prove2.me/submissions/42c9bae4-f7e6-400e-a7d8-5aa0b99c8a53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} {K : Type*} {V : ι → Type*}
variable [CommSemiring K] [∀ s, AddCommMonoid (V s)] [∀ s, Module K (V s)]
  {l m n : ι → Type*} [∀ s, Fintype (l s)] [∀ s, Fintype (m s)]
namespace GlobalTheory
theorem _root_.solution [∀ s, DecidableEq (m s)] (x : ∀ s, m s → V s) (d : ∀ s, m s → K) :
    frameMul x (fun s => Matrix.diagonal (d s)) = fun s j => d s j • x s j := by
  funext s j
  simp [frameMul, Matrix.diagonal_apply, ite_smul]
end GlobalTheory
