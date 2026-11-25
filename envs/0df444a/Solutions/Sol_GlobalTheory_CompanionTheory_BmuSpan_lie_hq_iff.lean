-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuSpan.lie_hq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:26.916122+00:00
-- url     : https://prove2.me/submissions/bd474ea7-c439-4f54-a754-71cc0f0e3a27

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SpanGenerators
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_hq_apply
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_BmuSpan_hq_apply__0093c439790b

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
theorem _root_.solution (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Lie (Hq k r) X ↔ ∀ i j, star (X (pr k r j) i) + X (pr k r i) j = 0 := by
  have h : ∀ i j, (Xᴴ * Hq k r + Hq k r * X) i j = star (X (pr k r j) i) + X (pr k r i) j := by
    intro i j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    congr 1
    · simp [hq_apply' _ j, conjTranspose_apply]
    · simp [hq_apply i]
  unfold Lie
  rw [← Matrix.ext_iff]
  simp only [h, Matrix.zero_apply]
end GlobalTheory.CompanionTheory.BmuSpan
