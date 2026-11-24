-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.int_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:27.553651+00:00
-- url     : https://prove2.me/submissions/b5eade89-e36c-4aed-a17f-29e39f7eca2d

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
    (ha : ∀ i j, ‖a i j‖ ≤ 1) (hb : ∀ i j, ‖b i j‖ ≤ 1) : ∀ i j, ‖(a + b) i j‖ ≤ 1 := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i j) (hb i j))
end GlobalTheory.CompanionTheory.Wedge
