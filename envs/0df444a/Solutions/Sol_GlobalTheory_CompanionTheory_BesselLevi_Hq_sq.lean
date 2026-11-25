-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselLevi.Hq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:51:45.746074+00:00
-- url     : https://prove2.me/submissions/c8d78962-fa46-4c97-9f8f-6dc8ee05ac5b

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_pr_pr
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_Hq_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_Hq_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselLevi
namespace GlobalTheory.CompanionTheory.BesselLevi
theorem _root_.solution (k r : ℕ) : Hq k r * Hq k r = 1 := by
  ext i j
  rw [Hq_mul_apply, Hq_apply, pr_pr, Matrix.one_apply]
end GlobalTheory.CompanionTheory.BesselLevi
