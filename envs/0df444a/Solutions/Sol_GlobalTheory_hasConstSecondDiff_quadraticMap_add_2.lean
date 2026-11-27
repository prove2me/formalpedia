-- Prove2me | solution 2 for GlobalTheory.hasConstSecondDiff_quadraticMap_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:41.800202+00:00
-- url     : https://prove2.me/submissions/ede3acba-58d6-4560-96c7-5697ae7be050

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
namespace GlobalTheory
theorem _root_.solution (Q : QuadraticMap ℤ X A) (c : A) :
    HasConstSecondDiff fun x => Q x + c := by
  have key : ∀ a μ ν, secondDiff (fun x => Q x + c) a μ ν = QuadraticMap.polar Q μ ν := by
    intro a μ ν
    simp only [secondDiff, QuadraticMap.map_add Q, QuadraticMap.polar_add_left]
    abel
  intro a a' μ ν
  rw [key, key]
end GlobalTheory
