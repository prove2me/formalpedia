-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.right_factor_action_diag_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:31.304739+00:00
-- url     : https://prove2.me/submissions/f61e9a14-840e-492d-b4a4-a9cbfa7ad0f8

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
theorem _root_.solution (T : Module.End ℂ V) : (on2 (dOp κ T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := rfl
end GlobalTheory.CompanionTheory.ZuckCasSplit
