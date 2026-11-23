-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.int_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:05.427075+00:00
-- url     : https://prove2.me/submissions/cf7f6df7-f5e0-4296-9d47-c3f3178b35c0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution [IsUltrametricDist K] [Fintype κ] {a : Matrix ι κ K} {b : Matrix κ ι' K}
    (ha : ∀ i j, ‖a i j‖ ≤ 1) (hb : ∀ i j, ‖b i j‖ ≤ 1) : ∀ i j, ‖(a * b) i j‖ ≤ 1 := by
  intro i j
  rw [mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (ha i k) (norm_nonneg _) (hb k j)
end GlobalTheory.CompanionTheory.Wedge
