-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuAdapt.A_zp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:36:55.721142+00:00
-- url     : https://prove2.me/submissions/a1524eb3-21ba-488e-a020-62e2a1334219

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_Hpk_val

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
theorem _root_.solution (hk : 1 ≤ k) (hi : i.val ≠ r) (hj : j.val = r) : Hpk k r i j = 0 := by
  rw [Hpk_val]; split_ifs <;> first | (exfalso; omega) | rfl
end GlobalTheory.CompanionTheory.BmuAdapt
