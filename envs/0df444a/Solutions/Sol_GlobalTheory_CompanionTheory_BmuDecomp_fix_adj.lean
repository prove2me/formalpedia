-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.fix_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:22:39.893434+00:00
-- url     : https://prove2.me/submissions/5b75beb2-f94a-4180-af66-7ea10290db64

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
theorem _root_.solution {A B P : Matrix (Fin n) (Fin n) ℂ} (hP : Pᴴ * A * P = B) {v w : Fin n → ℂ} (hv : P *ᵥ v = v)
    (hA : A *ᵥ v = w) (hB : B *ᵥ v = w) : Pᴴ *ᵥ w = w := by
  conv_rhs => rw [← hB, ← hP, ← mulVec_mulVec, ← mulVec_mulVec, hv, hA]
end GlobalTheory.CompanionTheory.BmuDecomp
