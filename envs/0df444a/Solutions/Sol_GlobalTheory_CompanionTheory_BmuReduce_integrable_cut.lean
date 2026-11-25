-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuReduce.integrable_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:08.43503+00:00
-- url     : https://prove2.me/submissions/8a16656e-d5e5-40a8-ac7a-7401b0cd2c7c

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ReductionOfDerivedSeries
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul


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
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace GlobalTheory.CompanionTheory.BmuReduce
theorem _root_.solution {d : ℕ} {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    {f : (Fin d → ℝ) → H} (hf : Continuous f) : Integrable (fun t => ψ t • f t) :=
  (hψ.smul hf).integrable_of_hasCompactSupport hc.smul_right
end GlobalTheory.CompanionTheory.BmuReduce
