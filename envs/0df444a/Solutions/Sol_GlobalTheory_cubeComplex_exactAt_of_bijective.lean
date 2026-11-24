-- Prove2me | solution 1 for GlobalTheory.cubeComplex_exactAt_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:14.11181+00:00
-- url     : https://prove2.me/submissions/a48dc2db-dfc2-493c-952b-b90d0c95d6ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_Cube_eq_zero_of_d_eq_zero
import Theorems.Thm_GlobalTheory_Cube_exact_d_of_bijective
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_iff

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → Function.Bijective (Cube.res A (Finset.subset_insert i s)))
    (p : ℕ) : (cubeComplex A).ExactAt p := by
  cases p with
  | zero =>
    rw [cubeComplex_exactAt_zero_iff', injective_iff_map_eq_zero]
    intro x hx
    refine Cube.eq_zero_of_d_eq_zero A i (fun s hs => (hA s hs).1) x hx fun s hs => ?_
    rw [Finset.card_eq_zero.1 s.2] at hs
    simp at hs
  | succ p => exact (cubeComplex_exactAt_succ_iff A p).2 (Cube.exact_d_of_bijective A i hA p)
end GlobalTheory
