-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckToRaw.act_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:23.952594+00:00
-- url     : https://prove2.me/submissions/cb97b3fe-8f6c-49b0-9d92-d87ff8274a08

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_act_coe

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckToRaw
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckToRaw
theorem _root_.solution (U : URep k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ GG k r) (x : M (one U)) :
    (CompanionTheory.Zuck.act (one U) g x () : U.R.H) = U.R.σ g (x ()) := by
  rw [act_coe (one U) hg]
  simp [BranchingSupport.act]
end GlobalTheory.CompanionTheory.ZuckToRaw
