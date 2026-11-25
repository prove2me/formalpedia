-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.prodEx_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:56:55.213615+00:00
-- url     : https://prove2.me/submissions/3d0e8c1a-f541-4488-9491-430d146a188b

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence

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
theorem _root_.solution {d : ℕ} (X : Fin (d + 1) → Mat n) (t : Fin (d + 1) → ℝ) :
    prodEx X t = ex (X 0) (t 0) * prodEx (fun j => X j.succ) (fun j => t j.succ) := by
  simp only [prodEx, List.ofFn_succ, List.prod_cons]
end GlobalTheory.CompanionTheory.ProdExChart
