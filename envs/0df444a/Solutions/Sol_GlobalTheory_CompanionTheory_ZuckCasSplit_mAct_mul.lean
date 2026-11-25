-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.mAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:34.520719+00:00
-- url     : https://prove2.me/submissions/549cf034-d82f-4705-b45e-d55d488a16c5

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
theorem _root_.solution (A B : Matrix ι ι ℂ) : (mAct A * mAct B : Module.End ℂ (ι → V)) = mAct (A * B) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [Module.End.mul_apply, mAct_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm
end GlobalTheory.CompanionTheory.ZuckCasSplit
