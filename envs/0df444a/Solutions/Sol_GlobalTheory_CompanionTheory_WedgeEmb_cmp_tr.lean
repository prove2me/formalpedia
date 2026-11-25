-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.cmp_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:54.507163+00:00
-- url     : https://prove2.me/submissions/aa130e4e-3c38-4f27-8af1-c818840f9c7f

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality

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
theorem _root_.solution (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : BranchingSupport.cmp l gᵀ = (BranchingSupport.cmp l g)ᵀ := by
  ext I J
  simp only [BranchingSupport.cmp, Matrix.transpose_apply]
  rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_transpose]
end GlobalTheory.CompanionTheory.WedgeEmb
