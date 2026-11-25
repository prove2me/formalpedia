-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.mul_single_mul_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:58:33.285451+00:00
-- url     : https://prove2.me/submissions/4e098640-080f-46a8-b7ea-83cc0bbc340a

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
namespace GlobalTheory.CompanionTheory.BmuRootVec
theorem _root_.solution {n : ℕ} (A B : Mat n) (a b i l : Fin n) (c : ℂ) :
    (A * single a b c * B) i l = A i a * c * B b l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    rw [Matrix.mul_single_apply_of_ne (hbj := hj), zero_mul]
  · simp
end GlobalTheory.CompanionTheory.BmuRootVec
