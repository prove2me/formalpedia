-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuReduce.cut_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:48.86573+00:00
-- url     : https://prove2.me/submissions/08ed228b-fe30-48fd-bc8a-dc4a067d1d11

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U) {φ a : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiff ℝ ∞ (fun t => φ t * a t) ∧ HasCompactSupport (fun t => φ t * a t) ∧
      tsupport (fun t => φ t * a t) ⊆ U := by
  have h1 : tsupport (fun t => φ t * a t) ⊆ U := (tsupport_mul_subset_left (f := φ) (g := a)).trans hs
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hc.mul_right, h1⟩
  by_cases hx : x ∈ tsupport (fun t => φ t * a t)
  · exact hφ.contDiffAt.mul (ha.contDiffAt (hU.mem_nhds (h1 hx)))
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hx)
end GlobalTheory.CompanionTheory.BmuReduce
