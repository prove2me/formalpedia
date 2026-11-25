-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckMatHom.dOp_mAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:27:35.001989+00:00
-- url     : https://prove2.me/submissions/2a2a69c7-b5a1-413c-b8b1-058329e927ab

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
theorem _root_.solution {ι ι' V V' : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (A : Matrix ι' ι ℂ) (T : V →ₗ[ℂ] V') (x : ι → V) :
    dOp ι' T (mAct A x) = mAct A (dOp ι T x) := by
  funext c
  have h : ∀ (κ : Type) (y : κ → V) (e : κ), dOp κ T y e = T (y e) := fun _ _ _ => rfl
  simp only [h, mAct_coord, map_sum, map_smul]
end GlobalTheory.CompanionTheory.ZuckMatHom
