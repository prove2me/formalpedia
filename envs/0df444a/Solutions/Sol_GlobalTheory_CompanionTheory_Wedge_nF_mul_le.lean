-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.nF_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:11.103834+00:00
-- url     : https://prove2.me/submissions/3c55c1f8-6198-4aeb-922a-4f257b49d423

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Wedge_nF_nonneg__274c325c4b7e
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Wedge_sz_nonneg__758761aca7cd
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_sz_le_one

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
theorem _root_.solution (hM : MulF) [IsUltrametricDist K] [Fintype ι] [Fintype ι'] [Fintype κ]
    [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (hg : ∀ i j, ‖g i j‖ ≤ 1) :
    nF (g * A) ≤ nF A := by
  refine ((hM K ι ι' κ A).1 g).trans ?_
  have h1 : sz g ^ Fintype.card κ ≤ 1 := pow_le_one₀ (sz_nonneg' g) (sz_le_one hg)
  simpa using mul_le_mul_of_nonneg_right h1 (nF_nonneg' A)
end GlobalTheory.CompanionTheory.Wedge
