-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.sum_pts_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:51.436804+00:00
-- url     : https://prove2.me/submissions/dd236cf5-7978-4d03-8c07-c9f4b3aec151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Theorems.Thm_GlobalTheory_HermitianGauss_mem_pts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermitianGauss.mem_pts

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
namespace GlobalTheory.HermitianGauss
theorem _root_.solution (B : Submodule R M) (f : M → ℂ) {z : M} (hz : z ∈ B) :
    ∑ y ∈ pts B, f (y + z) = ∑ y ∈ pts B, f y := by
  refine Finset.sum_nbij' (fun y => y + z) (fun y => y - z) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact mem_pts.mpr (B.add_mem (mem_pts.mp ha) hz)
  · intro a ha; exact mem_pts.mpr (B.sub_mem (mem_pts.mp ha) hz)
  · intro a _; exact add_sub_cancel_right a z
  · intro a _; exact sub_add_cancel a z
  · intro a _; rfl
end GlobalTheory.HermitianGauss
