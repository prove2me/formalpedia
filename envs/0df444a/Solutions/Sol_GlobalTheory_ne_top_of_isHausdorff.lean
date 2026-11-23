-- Prove2me | solution 1 for GlobalTheory.ne_top_of_isHausdorff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:00.129277+00:00
-- url     : https://prove2.me/submissions/e4f2f65f-3fda-4c24-b48c-0322930a661b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]
namespace GlobalTheory
theorem _root_.solution (I : Ideal R) [IsHausdorff I R] : I ≠ ⊤ := by
  rintro rfl
  exact not_subsingleton R (IsHausdorff.subsingleton (R := R) (M := R) ‹_›)
end GlobalTheory
