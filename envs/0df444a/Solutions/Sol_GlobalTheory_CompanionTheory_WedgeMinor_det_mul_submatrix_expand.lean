-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeMinor.det_mul_submatrix_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:56:07.054666+00:00
-- url     : https://prove2.me/submissions/2706b184-2a69-4426-8e26-6e00b644cd8f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeMinor
namespace GlobalTheory.CompanionTheory.WedgeMinor
theorem _root_.solution {K ι ι' κ : Type} [CommRing K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ((g * A).submatrix t id).det =
      ∑ s : κ → ι, (∏ i, g (t i) (s i)) * (A.submatrix s id).det := by
  have h : ((g * A).submatrix t id : κ → κ → K) = fun i => ∑ k, g (t i) k • A k := by
    funext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have key : ∀ M : Matrix κ κ K,
      M.det = (detRowAlternating (R := K) (n := κ)).toMultilinearMap M := fun _ => rfl
  rw [key, h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl
end GlobalTheory.CompanionTheory.WedgeMinor
