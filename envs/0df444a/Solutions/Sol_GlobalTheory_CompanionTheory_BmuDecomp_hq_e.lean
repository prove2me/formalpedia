-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.hq_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:57:52.645339+00:00
-- url     : https://prove2.me/submissions/0d31a8c3-c466-477a-94bb-9cd88fbdb647

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
theorem _root_.solution (a : Fin r) : Hq k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
  ext i
  have := a.isLt
  have := i.isLt
  simp only [bvec, mulVec_single_one, Matrix.col_apply, Pi.single_apply, Hq, outer, eI, esI, Fin.ext_iff]
  split_ifs <;> first | omega | rfl
end GlobalTheory.CompanionTheory.BmuDecomp
