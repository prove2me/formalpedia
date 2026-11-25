-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuSpan.lie_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:20.777412+00:00
-- url     : https://prove2.me/submissions/79c21960-39db-4976-9fb7-7bfd6979e87c

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
theorem _root_.solution {A X Y : Matrix (Fin n) (Fin n) ℂ} (hX : Lie A X) (hY : Lie A Y) : Lie A (X - Y) := by
  unfold Lie at *
  have : (X - Y)ᴴ * A + A * (X - Y) = (Xᴴ * A + A * X) - (Yᴴ * A + A * Y) := by
    rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [this, hX, hY, sub_zero]
end GlobalTheory.CompanionTheory.BmuSpan
