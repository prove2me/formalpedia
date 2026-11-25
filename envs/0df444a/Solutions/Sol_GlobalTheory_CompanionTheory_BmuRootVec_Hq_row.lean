-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.Hq_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:11.109524+00:00
-- url     : https://prove2.me/submissions/1b2eef3c-8f39-411c-9543-1074918f2511

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


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
    (l : Fin (2 * r + k + 1)) : Hq k r i l = if l = i' then 1 else 0 := by
  simp only [Hq, hi, if_true, Fin.ext_iff]
  congr 1
  apply propext; omega
end GlobalTheory.CompanionTheory.BmuRootVec
