-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.single_mul_Hq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:21.507943+00:00
-- url     : https://prove2.me/submissions/2e23519e-16b1-475e-a2f0-03961fc49f21

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_mul_single_mul_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_Hq_row

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
    (l : Fin (2 * r + k + 1)) (c : ℂ) : single l i c * Hq k r = single l i' c := by
  ext p q
  have := mul_single_mul_entry 1 (Hq k r) l i p q c
  rw [Matrix.one_mul] at this
  rw [this, Hq_row hi h, Matrix.one_apply, Matrix.single_apply]
  by_cases h1 : l = p <;> by_cases h2 : i' = q <;> simp [h1, h2, @eq_comm _ p l, @eq_comm _ q i']
end GlobalTheory.CompanionTheory.BmuRootVec
