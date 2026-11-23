-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.int_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:05.92936+00:00
-- url     : https://prove2.me/submissions/927de8b7-be15-45cd-8af5-96b4c32be6f2

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
theorem _root_.solution [IsUltrametricDist K] {a b : Matrix ι κ K}
    (ha : ∀ i j, ‖a i j‖ ≤ 1) (hb : ∀ i j, ‖b i j‖ ≤ 1) : ∀ i j, ‖(a - b) i j‖ ≤ 1 := fun i j =>
  by
  have h : (a - b) i j = a i j + -b i j := by simp [sub_eq_add_neg]
  rw [h]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i j) (by simpa using hb i j))
end GlobalTheory.CompanionTheory.Wedge
