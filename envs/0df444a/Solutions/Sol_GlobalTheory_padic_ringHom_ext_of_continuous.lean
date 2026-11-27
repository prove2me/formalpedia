-- Prove2me | solution 1 for GlobalTheory.padic_ringHom_ext_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:43:06.323835+00:00
-- url     : https://prove2.me/submissions/3d5383ff-5489-4cb4-8963-d0066a55211a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {C : Type*} [NormedField C] (p : ℕ) [Fact p.Prime]
    {j₁ j₂ : ℚ_[p] →+* C} (h₁ : Continuous j₁) (h₂ : Continuous j₂) : j₁ = j₂ := by
  refine RingHom.ext fun x => congrFun ((Padic.denseRange_ratCast p).equalizer h₁ h₂ ?_) x
  ext q
  simp
end GlobalTheory
