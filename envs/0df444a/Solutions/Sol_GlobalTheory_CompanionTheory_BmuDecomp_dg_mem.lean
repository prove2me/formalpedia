-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.dg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:23.913498+00:00
-- url     : https://prove2.me/submissions/63318d94-b94f-4fcf-94f7-2909c886d64d

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
theorem _root_.solution {d : Fin (2 * r + k + 1) → ℝ} (hd : IsTor k r d) : dg d ∈ UH (Hq k r) := by
  obtain ⟨-, h2, h3, -⟩ := hd
  show (dg d)ᴴ * Hq k r * dg d = Hq k r
  ext i j
  simp only [dg, diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Hq]
  split_ifs with h h' h'
  · rw [mul_one, ← Complex.ofReal_mul, h2 i j h h', Complex.ofReal_one]
  · simp
  · subst h'; rw [h3 i h]; simp
  · simp
end GlobalTheory.CompanionTheory.BmuDecomp
