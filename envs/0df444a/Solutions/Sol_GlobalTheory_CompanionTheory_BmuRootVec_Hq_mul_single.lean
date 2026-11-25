-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.Hq_mul_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:38.306805+00:00
-- url     : https://prove2.me/submissions/b6126c9d-53ca-4ed0-9ae9-f76490236d92

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_mul_single_mul_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_Hq_col

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
theorem _root_.solution {i i' : Fin (2 * r + k + 1)} (hi : outer k r i) (h : i.val + i'.val = 2 * r + k)
    (l : Fin (2 * r + k + 1)) (c : ℂ) : Hq k r * single i l c = single i' l c := by
  ext p q
  have := mul_single_mul_entry (Hq k r) 1 i l p q c
  rw [Matrix.mul_one] at this
  rw [this, Hq_col hi h, Matrix.one_apply, Matrix.single_apply]
  by_cases h1 : i' = p <;> by_cases h2 : l = q <;> simp [h1, h2, @eq_comm _ p i']
end GlobalTheory.CompanionTheory.BmuRootVec
