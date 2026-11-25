-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckToRaw.extZ_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:26:43.520475+00:00
-- url     : https://prove2.me/submissions/0900a638-eb90-414c-937e-aad69f26d8af

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
theorem _root_.solution {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.smSub) :
    extZ f (y : R.H) = (f y : R'.H) := by
  simp only [extZ, dif_pos y.2]
end GlobalTheory.CompanionTheory.ZuckToRaw
