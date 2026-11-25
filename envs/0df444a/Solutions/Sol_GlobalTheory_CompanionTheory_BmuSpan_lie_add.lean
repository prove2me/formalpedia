-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuSpan.lie_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:40:43.239162+00:00
-- url     : https://prove2.me/submissions/569e8fe2-9fe3-43dc-bc4e-4fa73f049614

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SpanGenerators

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
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BmuSpan
theorem _root_.solution {A X Y : Matrix (Fin n) (Fin n) ℂ} (hX : Lie A X) (hY : Lie A Y) : Lie A (X + Y) := by
  unfold Lie at *
  have : (X + Y)ᴴ * A + A * (X + Y) = (Xᴴ * A + A * X) + (Yᴴ * A + A * Y) := by
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
  rw [this, hX, hY, add_zero]
end GlobalTheory.CompanionTheory.BmuSpan
