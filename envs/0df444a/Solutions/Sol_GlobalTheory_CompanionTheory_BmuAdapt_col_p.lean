-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuAdapt.col_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:25.594551+00:00
-- url     : https://prove2.me/submissions/79766f59-b7e3-40fc-9167-60cbd3dc247b

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
theorem _root_.solution (hj : j.val = r) :
    col k r j = s2 • (bvec (wI k r 0) + bvec (wI k r (Fin.last k))) := by
  rw [col, if_pos hj]
end GlobalTheory.CompanionTheory.BmuAdapt
