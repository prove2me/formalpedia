-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.right_factor_action_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:52:02.245529+00:00
-- url     : https://prove2.me/submissions/2292b15b-a057-4528-8c19-3717b6a19bba

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting

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
theorem _root_.solution {α : Type} (s : Finset α) (T : α → Module.End ℂ (κ → V)) :
    (on2 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on2 (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on2]
end GlobalTheory.CompanionTheory.ZuckCasSplit
