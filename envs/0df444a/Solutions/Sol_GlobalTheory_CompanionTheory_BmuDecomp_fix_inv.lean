-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.fix_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:01.92492+00:00
-- url     : https://prove2.me/submissions/c4077994-48b4-4ffc-8c6f-96d2d043d463

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuDecomp
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BmuDecomp
theorem _root_.solution {P Q : Matrix (Fin n) (Fin n) ℂ} (h : Q * P = 1) {v : Fin n → ℂ} (hv : P *ᵥ v = v) :
    Q *ᵥ v = v := by
  conv_lhs => rw [← hv]
  rw [mulVec_mulVec, h, one_mulVec]
end GlobalTheory.CompanionTheory.BmuDecomp
