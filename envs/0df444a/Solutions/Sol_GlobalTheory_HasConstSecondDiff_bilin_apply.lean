-- Prove2me | solution 1 for GlobalTheory.HasConstSecondDiff.bilin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:55.809428+00:00
-- url     : https://prove2.me/submissions/af66f00d-8dd1-4c07-adc3-623f0493928c

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
theorem _root_.solution (h : HasConstSecondDiff f) (a μ ν : X) :
    h.bilin μ ν = f (a + μ + ν) - f (a + μ) - f (a + ν) + f a :=
  h 0 a μ ν
end GlobalTheory.HasConstSecondDiff
