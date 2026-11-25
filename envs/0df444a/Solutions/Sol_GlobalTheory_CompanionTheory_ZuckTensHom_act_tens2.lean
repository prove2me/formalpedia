-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckTensHom.act_tens2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:20.180221+00:00
-- url     : https://prove2.me/submissions/90dfcf52-1eea-4ea2-8c9e-8ae70b6a42d3

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SnTens2
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckTensHom_act_apply

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
theorem _root_.solution (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (E.tens F, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (e', c')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens]
end GlobalTheory.CompanionTheory.ZuckTensHom
