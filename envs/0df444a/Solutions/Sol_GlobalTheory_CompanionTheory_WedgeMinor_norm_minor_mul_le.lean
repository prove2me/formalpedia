-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeMinor.norm_minor_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:12:36.141092+00:00
-- url     : https://prove2.me/submissions/6888b33c-0da9-4010-bb5a-2042aa8889c5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_det_mul_submatrix_expand
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_sz_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_le_sz
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_nF_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_le_nF

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
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ‖((g * A).submatrix t id).det‖ ≤ sz g ^ Fintype.card κ * nF A := by
  rw [det_mul_submatrix_expand]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A)) fun s _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul ?_ (le_nF A s) (norm_nonneg _) (pow_nonneg (sz_nonneg g) _)
  calc ∏ i, ‖g (t i) (s i)‖ ≤ ∏ _i : κ, sz g :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => le_sz g _ _
    _ = sz g ^ Fintype.card κ := by simp
end GlobalTheory.CompanionTheory.WedgeMinor
