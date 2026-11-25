-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.dOp_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:27:01.543285+00:00
-- url     : https://prove2.me/submissions/8c7f947e-3c72-46e6-82e4-270d9fb26817

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
theorem _root_.solution {α : Type} (s : Finset α) (T : α → Module.End ℂ V) :
    (dOp ι (∑ a ∈ s, T a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, dOp ι (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [dOp]
end GlobalTheory.CompanionTheory.ZuckCasSplit
