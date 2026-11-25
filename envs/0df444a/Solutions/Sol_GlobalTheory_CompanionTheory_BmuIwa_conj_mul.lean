-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuIwa.conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:48:25.66667+00:00
-- url     : https://prove2.me/submissions/d4ff2e2f-c460-4814-9ee4-9c492931eb21

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwasawaDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuIwa
open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory.CompanionTheory.BmuIwa
theorem _root_.solution {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A) * g = 1 := by
  calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hA]
end GlobalTheory.CompanionTheory.BmuIwa
