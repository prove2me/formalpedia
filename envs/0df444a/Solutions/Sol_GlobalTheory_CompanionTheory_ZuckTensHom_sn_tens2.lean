-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckTensHom.sn_tens2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:00:18.743976+00:00
-- url     : https://prove2.me/submissions/faae8531-3176-4bee-a8ed-3953d0618d25

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SnTens2

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckTensHom
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckTensHom
theorem _root_.solution (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (E.tens F, U)) :
    sn (E.tens F, U) W x = ∑ e, sn (F, U) W (fun c => x (e, c)) := by
  simp only [CompanionTheory.Zuck.sn]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]
end GlobalTheory.CompanionTheory.ZuckTensHom
