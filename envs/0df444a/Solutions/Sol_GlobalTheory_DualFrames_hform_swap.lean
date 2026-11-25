-- Prove2me | solution 1 for GlobalTheory.DualFrames.hform_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:10.089243+00:00
-- url     : https://prove2.me/submissions/35b49753-3734-4943-86c2-14a238bdff3d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DualOfDualFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.DualFrames
variable {A : Type} [CommRing A] {k : ℕ}
namespace GlobalTheory.DualFrames
theorem _root_.solution (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) (J : Matrix (Fin k) (Fin k) A)
    (hJ : IsHerm τ J) (x y : Fin k → A) : τ (hform τ J x y) = hform τ J y x := by
  unfold IsHerm cT at hJ
  have hJ' : ∀ i j, τ (J i j) = J j i := by
    intro i j
    simpa using congrFun (congrFun hJ j) i
  unfold hform
  simp only [map_sum, map_mul, hτ, hJ']
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.DualFrames
