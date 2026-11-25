-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.left_inv_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:17.683836+00:00
-- url     : https://prove2.me/submissions/002e3382-6527-476e-af4a-64e4e2f8b0c4

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
theorem _root_.solution {Hm g : Mat n} (h : Hm * Hm = 1) (hg : g ∈ UH Hm) :
    Hm * gᴴ * Hm * g = 1 := by
  have hg' : gᴴ * Hm * g = Hm := hg
  calc Hm * gᴴ * Hm * g = Hm * (gᴴ * Hm * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', h]
end GlobalTheory.CompanionTheory.ProdExChart
