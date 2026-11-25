-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:21:14.620222+00:00
-- url     : https://prove2.me/submissions/b0bacc19-7968-4697-be7b-2e3a5f573f76

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_first
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_cmp_tr
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_third

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeEmb
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.WedgeEmb
theorem _root_.solution : WedgeInt := by
  intro n m
  refine ⟨fun g => ⟨first g, ?_⟩, third⟩
  have h := congrArg Matrix.transpose (first (n := n) (m := m) gᵀ)
  simp only [Matrix.transpose_mul, cmp_tr, Matrix.transpose_transpose,
    Matrix.kroneckerMap_transpose] at h
  exact h.symm
end GlobalTheory.CompanionTheory.WedgeEmb
