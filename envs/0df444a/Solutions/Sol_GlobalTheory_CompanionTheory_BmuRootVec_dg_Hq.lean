-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.dg_Hq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:30.799658+00:00
-- url     : https://prove2.me/submissions/31bac47a-1175-4de0-94fa-393b6f81b558

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuRootVec
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuRootVec
theorem _root_.solution {d : Fin (2 * r + k + 1) → ℝ} (hd : IsTor k r d) :
    (dg d)ᴴ * Hq k r * dg d = Hq k r := by
  obtain ⟨-, h1, h2, -⟩ := hd
  ext i j
  simp only [dg, diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Hq]
  split_ifs with a b c
  · have := h1 i j a b
    rw [mul_one, ← Complex.ofReal_mul, this, Complex.ofReal_one]
  · simp
  · subst c; simp [h2 i a]
  · simp
end GlobalTheory.CompanionTheory.BmuRootVec
