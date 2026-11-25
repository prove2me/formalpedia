-- Prove2me | solution 1 for GlobalTheory.HasConstSecondDiff.bilin_comp_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:46.03303+00:00
-- url     : https://prove2.me/submissions/430e2b24-fb3d-4dda-9cfa-e36c98730199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst

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
open GlobalTheory.HasConstSecondDiff
variable {f : X → A}
namespace GlobalTheory.HasConstSecondDiff
theorem _root_.solution {A' : Type*} [AddCommGroup A'] (h : HasConstSecondDiff f) (v : A →+ A')
    (μ ν : X) : (h.comp_left v).bilin μ ν = v (h.bilin μ ν) := by
  simp [bilin_apply_zero]
end GlobalTheory.HasConstSecondDiff
