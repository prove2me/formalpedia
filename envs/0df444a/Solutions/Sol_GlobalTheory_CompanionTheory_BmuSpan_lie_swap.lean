-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuSpan.lie_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:29.536533+00:00
-- url     : https://prove2.me/submissions/d736392a-68ac-46ab-9b67-e6e62e5cae5a

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SpanGenerators
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_lie_hq_iff

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
theorem _root_.solution {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Lie (Hq k r) X) : Lie (Hq k r) (X.submatrix (pr k r) (pr k r)) := by
  rw [lie_hq_iff] at *
  intro i j
  exact hX (pr k r i) (pr k r j)
end GlobalTheory.CompanionTheory.BmuSpan
