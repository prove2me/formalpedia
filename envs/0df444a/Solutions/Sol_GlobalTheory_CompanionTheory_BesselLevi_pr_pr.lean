-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselLevi.pr_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:24:44.356806+00:00
-- url     : https://prove2.me/submissions/6a7d386f-a5c1-4d5d-ab17-f63e319faf6e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_pr_val
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : pr k r (pr k r i) = i := by
  have h1 := pr_val k r i
  have h2 := pr_val k r (pr k r i)
  apply Fin.ext
  omega
end GlobalTheory.CompanionTheory.BesselLevi
