-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeMinor.nF_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:10.396796+00:00
-- url     : https://prove2.me/submissions/91e099d9-11ff-4377-b633-000662842dd9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_sz_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_nF_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_norm_minor_mul_le

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
theorem _root_.solution {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) :
    nF (g * A) ≤ sz g ^ Fintype.card κ * nF A :=
  Real.iSup_le (fun t => norm_minor_mul_le g A t)
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A))
end GlobalTheory.CompanionTheory.WedgeMinor
