-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.isUnit_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:10:57.397697+00:00
-- url     : https://prove2.me/submissions/18b6bbc3-6d1f-497e-a685-6b3c1f69d525

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_left_inv_of_mem

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdExChart
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ProdExChart
theorem _root_.solution {Hm g : Mat n} (h : Hm * Hm = 1) (hg : g ∈ UH Hm) : IsUnit g :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse (left_inv_of_mem h hg))
end GlobalTheory.CompanionTheory.ProdExChart
