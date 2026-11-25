-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckToRaw.le_sn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:04:57.17516+00:00
-- url     : https://prove2.me/submissions/732eb447-26a4-4ec3-a665-69f365ff60d1

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex

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
theorem _root_.solution (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (x : M X) :
    ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖ ≤ sn X W x :=
  Finset.single_le_sum (f := fun c => ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
end GlobalTheory.CompanionTheory.ZuckToRaw
