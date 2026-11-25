-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDsDer.contDiff_dW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:04:17.762931+00:00
-- url     : https://prove2.me/submissions/a639908e-9515-4eb0-a1d6-1b98cc2c3a81

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesDerivation
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDsDer_contDiff_dL
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDsDer_contDiff_mulR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuDsDer
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
namespace GlobalTheory.CompanionTheory.BmuDsDer
theorem _root_.solution {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) : ∀ W, ContDiff ℝ ∞ (dW W Φ) := by
  intro W
  induction W with
  | nil => exact hΦ
  | cons Y W ih => exact contDiff_dL (contDiff_mulR Y) ih
end GlobalTheory.CompanionTheory.BmuDsDer
