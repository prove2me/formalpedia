-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.isTor_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:25.258507+00:00
-- url     : https://prove2.me/submissions/1aca02a6-7d98-4770-8c18-ffd5b66f2047

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
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuDecomp
theorem _root_.solution {t t' : Fin (2 * r + k + 1) → ℝ} (h : IsTor k r t) (h' : IsTor k r t') :
    IsTor k r (fun i => t i * t' i) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  refine ⟨fun i => mul_pos (h1 i) (g1 i), fun i j hi hij => ?_, fun i hi => ?_, ?_⟩
  · have a := h2 i j hi hij
    have b := g2 i j hi hij
    show t i * t' i * (t j * t' j) = 1
    rw [mul_mul_mul_comm, a, b, one_mul]
  · show t i * t' i = 1
    rw [h3 i hi, g3 i hi, one_mul]
  · exact mul_le_one₀ h4 (g1 _).le g4
end GlobalTheory.CompanionTheory.BmuDecomp
