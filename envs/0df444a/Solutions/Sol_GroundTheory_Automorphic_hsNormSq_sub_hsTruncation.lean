-- Prove2me | solution 1 for GroundTheory.Automorphic.hsNormSq_sub_hsTruncation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:41.681795+00:00
-- url     : https://prove2.me/submissions/86cbfeab-5c73-435c-804b-babe49be23ae

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Theorems.Thm_GroundTheory_Automorphic_sub_hsTruncation_apply_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap Filter Topology
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
omit [CompleteSpace K]
namespace GroundTheory.Automorphic
theorem _root_.solution (T : H →L[𝕜] K) (F : Finset (exists_hilbertBasis 𝕜 H).choose) :
    hsNormSq (T - hsTruncation (stdHilbertBasis 𝕜 H) T F) =
      ∑' i : {i // i ∉ F}, ‖T (stdHilbertBasis 𝕜 H i)‖ₑ ^ 2 := by
  classical
  rw [hsNormSq]
  refine Eq.trans ?_ (tsum_subtype ({i | i ∉ F} : Set _) (fun i => ‖T (stdHilbertBasis 𝕜 H i)‖ₑ ^ 2)).symm
  refine tsum_congr fun j => ?_
  rw [sub_hsTruncation_apply_basis]
  by_cases hj : j ∈ F
  · simp [hj]
  · simp [hj]
end GroundTheory.Automorphic
