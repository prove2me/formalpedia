-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.contDiff_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:57.107302+00:00
-- url     : https://prove2.me/submissions/776a0958-5ac9-4c5f-b73a-241c8966d098

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_contDiff_conjT
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_inv_of_mem

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
theorem _root_.solution {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {Hm : Mat n}
    (h : Hm * Hm = 1) {s : P → Mat n} (hs : ContDiff ℝ ∞ s) (hm : ∀ t, s t ∈ UH Hm) (Y : Mat n) :
    ContDiff ℝ ∞ (fun t => (s t)⁻¹ * Y * s t) := by
  have : (fun t => (s t)⁻¹ * Y * s t) = fun t => Hm * (s t)ᴴ * Hm * Y * s t :=
    funext fun t => by rw [inv_of_mem h (hm t)]
  rw [this]
  exact contDiff_mul' (contDiff_mul' (contDiff_mul' (contDiff_mul' contDiff_const
    (contDiff_conjT.comp hs)) contDiff_const) contDiff_const) hs
end GlobalTheory.CompanionTheory.ProdExChart
