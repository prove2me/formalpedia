-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.col_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:46.644049+00:00
-- url     : https://prove2.me/submissions/cd4e9c18-3c91-4f8e-9eb6-9d3bd753cefd

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
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BmuDecomp
theorem _root_.solution {P : Matrix (Fin n) (Fin n) ℂ} {i : Fin n} (h : P *ᵥ bvec i = bvec i) (j : Fin n) :
    P j i = if j = i then 1 else 0 := by
  have := congrFun h j
  simpa [bvec, Pi.single_apply] using this
end GlobalTheory.CompanionTheory.BmuDecomp
