-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuReduce.cut_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:40:19.173557+00:00
-- url     : https://prove2.me/submissions/15899fc2-8bc5-4b09-ab4e-f9c6d8d9ae3e

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (v : E) :
    ContDiff ℝ ∞ (fun t => fderiv ℝ φ t v) ∧ HasCompactSupport (fun t => fderiv ℝ φ t v) ∧
      tsupport (fun t => fderiv ℝ φ t v) ⊆ U :=
  ⟨(hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, hc.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans hs⟩
end GlobalTheory.CompanionTheory.BmuReduce
