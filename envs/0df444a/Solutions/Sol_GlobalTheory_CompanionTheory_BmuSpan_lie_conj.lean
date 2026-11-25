-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuSpan.lie_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:59.805654+00:00
-- url     : https://prove2.me/submissions/1f6cdb6a-eb9b-4849-99a5-2b3ff6b3ce5a

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
theorem _root_.solution {A B P Q X : Matrix (Fin n) (Fin n) ℂ} (hQ : Qᴴ * B * Q = A) (hQP : Q * P = 1)
    (hX : Lie B X) : Lie A (P * X * Q) := by
  unfold Lie at *
  have h1 : Pᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQP, conjTranspose_one]
  have c1 : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Pᴴ * (Qᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have c2 : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Q * (P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have : (P * X * Q)ᴴ * A + A * (P * X * Q) = Qᴴ * (Xᴴ * B + B * X) * Q := by
    rw [← hQ]
    simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, c1, c2]
  rw [this, hX, Matrix.mul_zero, Matrix.zero_mul]
end GlobalTheory.CompanionTheory.BmuSpan
