-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.contDiff_prodEx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:13.852453+00:00
-- url     : https://prove2.me/submissions/b0489a54-d968-4848-a920-c023667bb248

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_contDiff_ex
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_prodEx_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_contDiff_tail

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
theorem _root_.solution : ∀ {d : ℕ} (X : Fin d → Mat n), ContDiff ℝ ∞ (prodEx X)
  | 0, X => by
    have : prodEx X = fun _ => 1 := funext fun t => by simp [prodEx]
    rw [this]; exact contDiff_const
  | d + 1, X => by
    rw [show prodEx X = _ from funext (prodEx_succ X)]
    exact contDiff_mul' ((contDiff_ex (X 0)).comp (contDiff_apply ℝ ℝ 0))
      ((solution _).comp contDiff_tail)
end GlobalTheory.CompanionTheory.ProdExChart
