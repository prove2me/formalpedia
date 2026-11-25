-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCutLim.lieW_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:04:44.665968+00:00
-- url     : https://prove2.me/submissions/a36b4339-0c07-4e2e-8861-e7574160393b

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivationLimit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCutLim
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BesselCutLim
theorem _root_.solution {Hm : Mat n} {W : List (Mat n)} (hW : LieWd Hm W) : LieW (UH Hm) W :=
  fun X hX t => ex_mem_of_lie (hW X hX) t
end GlobalTheory.CompanionTheory.BesselCutLim
