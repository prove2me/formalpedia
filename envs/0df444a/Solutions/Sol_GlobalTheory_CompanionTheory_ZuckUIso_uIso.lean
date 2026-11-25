-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckUIso.uIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:33:48.29448+00:00
-- url     : https://prove2.me/submissions/1e65aab3-0b11-4b9d-a731-f9e23306b78a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIso
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckUIso_isHom_res
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckUIso
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckUIso
theorem _root_.solution : UIso := by
  rintro k r F U U' ⟨e, he⟩
  have he' : ∀ g ∈ GG k r, ∀ x, e.symm (U'.R.σ g x) = U.R.σ g (e.symm x) := fun g hg x => by
    apply e.injective
    rw [he g hg, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨dOp F.ι (res U U' (e.toContinuousLinearEquiv : U.R.H →L[ℂ] U'.R.H) he),
    dOp F.ι (res U' U (e.symm.toContinuousLinearEquiv : U'.R.H →L[ℂ] U.R.H) he'),
    isHom_res F U U' _ he e.norm_map, isHom_res F U' U _ he' e.symm.norm_map, ?_, ?_⟩
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.symm_apply_apply _)
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.apply_symm_apply _)
end GlobalTheory.CompanionTheory.ZuckUIso
