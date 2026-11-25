-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.col_of_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:20.930543+00:00
-- url     : https://prove2.me/submissions/0ca214a9-08bb-4abf-9041-8f8620446929

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
theorem _root_.solution {n : ℕ} {A : Mat n} {j : Fin n} (h : A *ᵥ bvec j = bvec j) (i : Fin n) :
    A i j = if i = j then 1 else 0 := by
  have := congrFun h i
  simpa [bvec, Pi.single_apply] using this
end GlobalTheory.CompanionTheory.BmuRootVec
