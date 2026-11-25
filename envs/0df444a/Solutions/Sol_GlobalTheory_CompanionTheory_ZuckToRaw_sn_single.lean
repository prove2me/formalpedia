-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckToRaw.sn_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:51:04.110924+00:00
-- url     : https://prove2.me/submissions/ba0788a9-8ebe-45eb-b210-3df7fa06965a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_ZuckToRaw_dsigW_zero__89af3ac8d530

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
theorem _root_.solution (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (v : X.2.R.smSub) :
    sn X W (Pi.single c v) = ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (v : X.2.R.H)‖ := by
  unfold sn
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, ZeroMemClass.coe_zero, dsigW_zero', norm_zero]
  · simp
end GlobalTheory.CompanionTheory.ZuckToRaw
