-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.prodEx_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:23.506151+00:00
-- url     : https://prove2.me/submissions/8fffb8f5-2526-48b7-964e-b171080ce06a

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_prodEx_succ
import Theorems.Thm_CCRuleCW_UH_mul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie


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
theorem _root_.solution {Hm : Mat n} : ∀ {d : ℕ} (X : Fin d → Mat n), (∀ j, Lie Hm (X j)) →
    ∀ t, prodEx X t ∈ UH Hm
  | 0, X, _, t => by simp [prodEx, UH]
  | d + 1, X, hX, t => by
    rw [prodEx_succ]
    exact CCRuleCW.UH_mul Hm _ _ (ex_mem_of_lie (hX 0) _) (solution _ (fun j => hX j.succ) _)
end GlobalTheory.CompanionTheory.ProdExChart
