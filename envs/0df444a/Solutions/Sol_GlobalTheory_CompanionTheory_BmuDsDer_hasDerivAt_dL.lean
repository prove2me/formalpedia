-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDsDer.hasDerivAt_dL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:50.085017+00:00
-- url     : https://prove2.me/submissions/133a58af-8122-4275-b4cd-ab8dda94f7b5

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesDerivation

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
theorem _root_.solution {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) (Y g y : Mat n) :
    HasDerivAt (fun t => Φ (g * ex Y t, y)) (dL (fun g => g * Y) Φ (g, y)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (g * ex Y t, y)) (g * Y, (0 : Mat n)) 0 :=
    (hasDerivAt_mul_ex g Y).prodMk (hasDerivAt_const 0 y)
  have h0 : (g, y) = (g * ex Y 0, y) := by rw [ex_zero, mul_one]
  exact ((hΦ.differentiable (by simp)) (g, y)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ h0
end GlobalTheory.CompanionTheory.BmuDsDer
