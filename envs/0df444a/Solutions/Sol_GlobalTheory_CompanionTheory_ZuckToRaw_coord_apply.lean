-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckToRaw.coord_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:07.760222+00:00
-- url     : https://prove2.me/submissions/de84a389-5051-40cb-b528-17d105992ce4

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
theorem _root_.solution {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) (v : X.2.R.smSub) :
    coord f d c v = f (Pi.single c v) d := rfl
end GlobalTheory.CompanionTheory.ZuckToRaw
