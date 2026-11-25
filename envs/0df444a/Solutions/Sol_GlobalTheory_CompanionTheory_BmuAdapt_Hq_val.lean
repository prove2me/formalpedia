-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuAdapt.Hq_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:41.840682+00:00
-- url     : https://prove2.me/submissions/260a5ea4-7255-4f8b-a699-9af0ab87583e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuAdapt
variable {k r : ℕ} {i j : Fin (2 * r + k + 1)}
namespace GlobalTheory.CompanionTheory.BmuAdapt
theorem _root_.solution (i j : Fin (2 * r + k + 1)) : Hq k r i j =
    if i.val ≤ r ∨ r + k ≤ i.val then (if i.val + j.val = 2 * r + k then 1 else 0)
    else if i.val = j.val then 1 else 0 := by
  simp only [Hq, outer, Fin.ext_iff]
end GlobalTheory.CompanionTheory.BmuAdapt
