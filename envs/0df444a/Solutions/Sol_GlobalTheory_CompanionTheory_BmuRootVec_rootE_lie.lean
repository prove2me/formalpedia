-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.rootE_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:23.77161+00:00
-- url     : https://prove2.me/submissions/9f205153-c868-4c75-92dd-66f685f147bf

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_Hq_mul_single
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_single_mul_Hq

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
theorem _root_.solution (a : Fin r) (κ : ℂ) : Lie (Hq k r) (rootE k r a κ) := by
  have ha := a.isLt
  unfold Lie rootE
  rw [conjTranspose_sub, conjTranspose_single, conjTranspose_single, Matrix.sub_mul, Matrix.mul_sub,
    single_mul_Hq (i := eI k r a) (i' := esI k r a) (by simp only [outer, eI]; omega)
      (by simp only [eI, esI]; omega),
    single_mul_Hq (i := nxtS k r a) (i' := nxt k r a) (by simp only [outer, nxtS]; omega)
      (by simp only [nxtS, nxt]; omega),
    Hq_mul_single (i := eI k r a) (i' := esI k r a) (by simp only [outer, eI]; omega)
      (by simp only [eI, esI]; omega),
    Hq_mul_single (i := nxtS k r a) (i' := nxt k r a) (by simp only [outer, nxtS]; omega)
      (by simp only [nxtS, nxt]; omega)]
  simp
end GlobalTheory.CompanionTheory.BmuRootVec
