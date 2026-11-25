-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.rootE_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:28:47.21292+00:00
-- url     : https://prove2.me/submissions/50c5cdef-e16a-4e90-bc17-298a9df37922

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
theorem _root_.solution (hk : 1 ≤ k) (a : Fin r) (κ : ℂ) : rootE k r a κ * rootE k r a κ = 0 := by
  have ha := a.isLt
  unfold rootE
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    single_mul_single_of_ne (h := by simp only [nxt, eI, Ne, Fin.ext_iff]; omega),
    single_mul_single_of_ne (h := by simp only [nxt, nxtS, Ne, Fin.ext_iff]; omega),
    single_mul_single_of_ne (h := by simp only [esI, eI, Ne, Fin.ext_iff]; omega),
    single_mul_single_of_ne (h := by simp only [esI, nxtS, Ne, Fin.ext_iff]; omega)]
  simp
end GlobalTheory.CompanionTheory.BmuRootVec
