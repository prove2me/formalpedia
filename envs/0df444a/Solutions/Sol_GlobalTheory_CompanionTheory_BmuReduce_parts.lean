-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuReduce.parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:16.581439+00:00
-- url     : https://prove2.me/submissions/6cd511ee-a12a-499c-9bb9-4d94810accd9

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ReductionOfDerivedSeries
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuReduce_cut_fderiv
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuReduce_integrable_cut

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
theorem _root_.solution {d : ℕ} {ψ : (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {f : (Fin d → ℝ) → H} (hf : ContDiff ℝ ∞ f) (v : Fin d → ℝ) :
    ∫ t, ψ t • fderiv ℝ f t v = - ∫ t, fderiv ℝ ψ t v • f t := by
  obtain ⟨h1, h2, -⟩ := cut_fderiv hψ hc (Set.subset_univ _) v
  refine integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (integrable_cut h1.continuous h2 hf.continuous)
    (integrable_cut hψ.continuous hc ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))
    (integrable_cut hψ.continuous hc hf.continuous) (fun x _ => hψ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
end GlobalTheory.CompanionTheory.BmuReduce
