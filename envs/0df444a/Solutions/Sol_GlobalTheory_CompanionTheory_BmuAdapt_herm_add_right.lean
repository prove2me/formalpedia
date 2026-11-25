-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuAdapt.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:11.108423+00:00
-- url     : https://prove2.me/submissions/e5218225-6e0b-4078-be12-68e13b7bf2d9

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuAdapt
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.CompanionTheory.BmuAdapt
theorem _root_.solution (H : Matrix ι ι ℂ) (x y w : ι → ℂ) : herm H w (x + y) = herm H w x + herm H w y := by
  simp [herm, add_dotProduct]
end GlobalTheory.CompanionTheory.BmuAdapt
