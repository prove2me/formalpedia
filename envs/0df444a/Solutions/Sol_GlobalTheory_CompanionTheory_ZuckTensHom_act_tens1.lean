-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckTensHom.act_tens1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:15.566528+00:00
-- url     : https://prove2.me/submissions/db6ec060-7804-47c5-ad55-1ad81716d292

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
theorem _root_.solution (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (F.tens E, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (F.tens E, U) g x (c, e) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (c', e')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : F.ι × E.ι, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens, mul_comm]
end GlobalTheory.CompanionTheory.ZuckTensHom
