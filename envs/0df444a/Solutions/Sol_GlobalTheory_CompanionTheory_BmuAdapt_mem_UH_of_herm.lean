-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuAdapt.mem_UH_of_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:05:04.57644+00:00
-- url     : https://prove2.me/submissions/121e2065-2226-44ba-8c06-78a961ff68c5

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_herm_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_herm_single
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
variable [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.BmuAdapt
theorem _root_.solution {H g : Matrix ι ι ℂ} (h : ∀ x y, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) :
    gᴴ * H * g = H := by
  ext i j
  rw [← herm_single (gᴴ * H * g), ← herm_mulVec, h, herm_single]
end GlobalTheory.CompanionTheory.BmuAdapt
