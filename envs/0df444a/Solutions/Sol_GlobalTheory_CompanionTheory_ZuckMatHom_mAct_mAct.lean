-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckMatHom.mAct_mAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:17.401659+00:00
-- url     : https://prove2.me/submissions/796f16d8-2712-49c1-b15e-8386944265b8

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixHom
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckMatHom_mAct_coord

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
theorem _root_.solution {ι ι' ι'' V : Type} [Fintype ι] [Fintype ι'] [AddCommGroup V] [Module ℂ V]
    (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) (x : ι → V) :
    mAct A (mAct B x) = mAct (A * B) x := by
  funext c
  simp only [mAct_coord, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm
end GlobalTheory.CompanionTheory.ZuckMatHom
