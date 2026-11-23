-- Prove2me | solution 1 for GlobalTheory.TwoStepUnipotent.st_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:58.608121+00:00
-- url     : https://prove2.me/submissions/eb47cef4-3679-4569-ac59-b20f3c844c2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.TwoStepUnipotent
variable {S : Type} [Ring S] (st : S →+ S) (e₁ e₃ h : S)
variable {st e₁ e₃ h}
namespace GlobalTheory.TwoStepUnipotent
theorem _root_.solution (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) : st 1 = 1 := by
  have h1 := hm 1 (st 1)
  rw [one_mul, hi, one_mul] at h1
  exact h1.symm
end GlobalTheory.TwoStepUnipotent
