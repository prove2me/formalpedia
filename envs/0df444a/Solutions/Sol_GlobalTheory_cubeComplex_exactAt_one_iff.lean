-- Prove2me | solution 1 for GlobalTheory.cubeComplex_exactAt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:08.816194+00:00
-- url     : https://prove2.me/submissions/3504da50-1aa7-4e36-ad0c-cbd8a335555c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
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
theorem _root_.solution (A : Cube.{v} ι R) :
    (cubeComplex A).ExactAt 1 ↔ Function.Exact (Cube.aug A) (Cube.d A 1) := by
  rw [cubeComplex_exactAt_succ_iff A 0]
  refine forall_congr' fun x => iff_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, (Cube.d_zero_apply A y).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(Cube.termZeroEquiv A).symm a, by simp [Cube.d_zero_apply]⟩
end GlobalTheory
