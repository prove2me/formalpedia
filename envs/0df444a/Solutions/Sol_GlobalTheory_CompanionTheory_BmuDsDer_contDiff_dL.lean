-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDsDer.contDiff_dL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:47.672573+00:00
-- url     : https://prove2.me/submissions/bd576cd8-7ffd-4e31-ba6c-ca91f92ab571

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
variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.CompanionTheory.BmuDsDer
theorem _root_.solution {a : E → E} (ha : ContDiff ℝ ∞ a) {Φ : E × E' → V} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (dL a Φ) := by
  exact (contDiff_infty_iff_fderiv.1 hΦ).2.clm_apply ((ha.comp contDiff_fst).prodMk contDiff_const)
end GlobalTheory.CompanionTheory.BmuDsDer
