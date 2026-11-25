-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.left_factor_action_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:16:02.224927+00:00
-- url     : https://prove2.me/submissions/33ecd5b6-fc67-4219-a7c4-8d40f885b388

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_mAct_apply

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCasSplit
open Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk)
variable {k r : ℕ}
set_option linter.unusedSectionVars false
variable {ι κ V : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.ZuckCasSplit
theorem _root_.solution (A : Matrix ι ι ℂ) :
    (on1 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct (A ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on1, mAct_apply, Fintype.sum_prod_type, Matrix.one_apply, LinearMap.funLeft_apply, kroneckerMap]
end GlobalTheory.CompanionTheory.ZuckCasSplit
