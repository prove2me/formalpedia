-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.left_factor_action_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:03.751799+00:00
-- url     : https://prove2.me/submissions/3c1ecc55-b56d-4d94-820f-1faf854ca2eb

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
theorem _root_.solution (f g : Module.End ℂ (ι → V)) :
    (on1 (f * g) : Module.End ℂ (ι × κ → V)) = on1 f * on1 g := rfl
end GlobalTheory.CompanionTheory.ZuckCasSplit
