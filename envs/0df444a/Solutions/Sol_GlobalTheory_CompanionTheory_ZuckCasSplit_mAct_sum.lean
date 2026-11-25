-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.mAct_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:43:33.133832+00:00
-- url     : https://prove2.me/submissions/62db9e4c-8da4-44c9-9af3-dc75eaa8d291

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
theorem _root_.solution {α : Type} (s : Finset α) (A : α → Matrix ι ι ℂ) :
    (mAct (∑ a ∈ s, A a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, mAct (A a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, Matrix.sum_apply, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm
end GlobalTheory.CompanionTheory.ZuckCasSplit
