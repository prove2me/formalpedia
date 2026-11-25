-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.fix_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:53.034807+00:00
-- url     : https://prove2.me/submissions/d81912f2-e655-4bcd-8a0b-b59e3d759e1d

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
theorem _root_.solution {P Q : Matrix (Fin n) (Fin n) ℂ} {v : Fin n → ℂ} (hv : P *ᵥ v = v) (hw : Q *ᵥ v = v) :
    (P * Q) *ᵥ v = v := by
  rw [← mulVec_mulVec, hw, hv]
end GlobalTheory.CompanionTheory.BmuDecomp
