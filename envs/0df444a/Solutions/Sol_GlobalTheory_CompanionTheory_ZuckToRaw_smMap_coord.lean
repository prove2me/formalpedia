-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckToRaw.smMap_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:08.845556+00:00
-- url     : https://prove2.me/submissions/f435a744-cdc2-4a12-9223-88e526c43b42

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_smMap_extZ
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_sn_single
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_le_sn
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckToRaw_coord_apply

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
theorem _root_.solution {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hf : IsHom X Y f) (d : Y.1.ι) (c : X.1.ι) :
    SmMap X.2.R Y.2.R (extZ (coord f d c)) := by
  refine smMap_extZ _ fun W hW => ?_
  obtain ⟨C, Ws, h1, h2⟩ := hf.cont W hW
  refine ⟨C, Ws, h1, fun y => ?_⟩
  have := (le_sn Y W d _).trans (h2 (Pi.single c y))
  simpa only [sn_single, coord_apply] using this
end GlobalTheory.CompanionTheory.ZuckToRaw
