-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuSpan.lie_mask
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:11.450554+00:00
-- url     : https://prove2.me/submissions/383324e6-aa1f-422c-b87a-714e7cbec4bf

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SpanGenerators
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_lie_hq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_mask_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_mask_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu GlobalTheory.CompanionTheory.BmuDecomp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuSpan
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuSpan
theorem _root_.solution {p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Prop}
    (hp : ∀ i j, p (pr k r j) i → p (pr k r i) j) {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Lie (Hq k r) X) : Lie (Hq k r) (mask p X) := by
  rw [lie_hq_iff] at *
  intro i j
  by_cases h : p (pr k r j) i
  · rw [mask_pos h, mask_pos (hp i j h), hX]
  · rw [mask_neg h, mask_neg (fun h' => h (hp j i h'))]; simp
end GlobalTheory.CompanionTheory.BmuSpan
