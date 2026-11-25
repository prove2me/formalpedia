-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuReduce.contDiff_of_smOn_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:51:26.958894+00:00
-- url     : https://prove2.me/submissions/b4610fed-403f-407b-86d1-f9cb54d21504

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ReductionOfDerivedSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuReduce
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.BmuReduce
theorem _root_.solution {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : E → V} (hf : SmOn Set.univ f) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro a
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a (Set.mem_univ a)
  refine (hF.contDiffAt (hU.mem_nhds haU)).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds haU] with g hg
  exact hfF g hg (Set.mem_univ g)
end GlobalTheory.CompanionTheory.BmuReduce
