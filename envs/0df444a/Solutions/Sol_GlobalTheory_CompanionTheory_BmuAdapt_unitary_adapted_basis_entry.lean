-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuAdapt.unitary_adapted_basis_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:17:07.634873+00:00
-- url     : https://prove2.me/submissions/bb62a2ae-be18-47d8-9bc7-0e69deb10e26

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_herm_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_unitary_adapted_basis_apply_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuAdapt_herm_bvec
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
namespace GlobalTheory.CompanionTheory.BmuAdapt
theorem _root_.solution (k r : ℕ) (H : Mat (2 * r + k + 1)) (i j : Fin (2 * r + k + 1)) :
    ((G0 k r)ᴴ * H * G0 k r) i j = herm H (col k r j) (col k r i) := by
  rw [← herm_bvec ((G0 k r)ᴴ * H * G0 k r), ← herm_mulVec, unitary_adapted_basis_apply_basis, unitary_adapted_basis_apply_basis]
end GlobalTheory.CompanionTheory.BmuAdapt
