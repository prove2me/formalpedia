-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCutLim.tendsto_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:39:56.115125+00:00
-- url     : https://prove2.me/submissions/d9c25ee5-f6ce-487b-a1f5-5c8ea255c11e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivationLimit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul


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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure (PI.MtM n)}
    {f : PI.MtM n → E} (hf : Integrable f μ) {ρ : Mat n → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ) :
    Tendsto (fun N : ℕ => ∫ y : PI.MtM n, (ρ (((N : ℝ) + 1)⁻¹ • Matrix.of y) : ℂ) • f y ∂μ) atTop
      (𝓝 ((ρ 0 : ℂ) • ∫ y, f y ∂μ)) := by
  obtain ⟨C, hC⟩ := hρ.bounded_above_of_compact_support hc
  rw [← integral_smul]
  refine tendsto_integral_of_dominated_convergence (fun y => C * ‖f y‖) (fun N => ?_)
    (hf.norm.const_mul C) (fun N => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · have h1 : Continuous fun y : PI.MtM n => (ρ (((N : ℝ) + 1)⁻¹ • Matrix.of y) : ℂ) :=
      Complex.continuous_ofReal.comp (hρ.comp
        ((show Continuous fun y : PI.MtM n => (Matrix.of y : Mat n) from continuous_id).const_smul
          (((N : ℝ) + 1)⁻¹)))
    exact h1.aestronglyMeasurable.smul hf.1
  · rw [norm_smul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · refine Tendsto.smul_const ?_ _
    refine (Complex.continuous_ofReal.comp hρ).continuousAt.tendsto.comp ?_
    have h0 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h0.smul_const (Matrix.of y : Mat n)
end GlobalTheory.CompanionTheory.BesselCutLim
