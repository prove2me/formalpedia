-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckMatHom.mAct_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:04.176177+00:00
-- url     : https://prove2.me/submissions/6f4c0e4f-906c-4ef3-b811-3302a709459d

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixHom

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckMatHom
namespace GlobalTheory.CompanionTheory.ZuckMatHom
theorem _root_.solution {ι ι' V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (A : Matrix ι' ι ℂ)
    (x : ι → V) (c : ι') : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct, LinearMap.sum_apply]
end GlobalTheory.CompanionTheory.ZuckMatHom
