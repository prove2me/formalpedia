-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckDecTens.mAct_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:38.167568+00:00
-- url     : https://prove2.me/submissions/2498e002-a279-428b-99bc-4a26c12f48bb

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfTensorFromHomLaws

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckDecTens
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckDecTens
theorem _root_.solution {ι ι' V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (e : ι' → ι) :
    (mAct ((1 : Matrix ι ι ℂ).submatrix e id) : (ι → V) →ₗ[ℂ] (ι' → V)) = LinearMap.funLeft ℂ V e := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct, LinearMap.funLeft_apply, Matrix.one_apply]
end GlobalTheory.CompanionTheory.ZuckDecTens
