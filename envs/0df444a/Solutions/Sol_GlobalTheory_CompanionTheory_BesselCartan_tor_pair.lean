-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.tor_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:20.152913+00:00
-- url     : https://prove2.me/submissions/931a6323-a002-49f0-9988-dd6f3abc87d0

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCartan
open scoped ComplexOrder
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BesselCartan
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (u : ℝ) (hu : u ≠ 0) (i j : Fin (2 * r + k + 1))
    (hij : i.val + j.val = 2 * r + k) : tor k r u i * tor k r u j = 1 := by
  have hil := i.isLt
  have hjl := j.isLt
  unfold GlobalTheory.CompanionTheory.BesselCartan.tor
  split_ifs <;> first | (exfalso; omega) | simp [hu]
end GlobalTheory.CompanionTheory.BesselCartan
