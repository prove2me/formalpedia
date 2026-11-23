-- Prove2me | solution 1 for GlobalTheory.Cube.extend_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:21.807362+00:00
-- url     : https://prove2.me/submissions/3dc4ecc7-2179-4ed7-9ffd-c4012195aaa3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι R) {p : ℕ} (x : Term A p) {s : Finset ι}
    (h : s.card ≠ p) : extend A p x s = 0 := dif_neg h
end GlobalTheory.Cube
