-- Prove2me | solution 1 for GlobalTheory.PlaceModel.IsBichar.nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:58.214903+00:00
-- url     : https://prove2.me/submissions/4d057ad8-6a14-4527-a48c-09af0f53017f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
namespace IsBichar
theorem _root_.solution (h : IsBichar χ) (k : ℕ) (x y : G) : χ (k • x) y = χ x (k • y) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, h.zero_left, h.zero_right]
  | succ k ih => rw [succ_nsmul, succ_nsmul, h.left, h.right, ih]
end IsBichar
end GlobalTheory.PlaceModel
