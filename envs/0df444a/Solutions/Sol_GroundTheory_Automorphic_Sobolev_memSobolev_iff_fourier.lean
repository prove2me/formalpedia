-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memSobolev_iff_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:57.928617+00:00
-- url     : https://prove2.me/submissions/cbd019ec-9d64-415d-8d75-20725f28a064

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_apply_eq_integral
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_weight_smul_fourierFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {m : E → ℂ} {C s t : ℝ}
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : 𝓢'(E, F)) :
    MemSobolev s 2 u ↔ ∃ g : E → F, MemLp (fun ξ ↦ weight s ξ • g ξ) 2 (volume : Measure E) ∧
      ∀ φ : 𝓢(E, ℂ), 𝓕 u φ = ∫ ξ, φ ξ • g ξ := by
  constructor
  · intro hu
    set v : SobolevSpace E F s := SobolevSpace.mk u hu
    refine ⟨fourierFun v, ?_, fourier_apply_eq_integral v⟩
    have : (fun ξ ↦ weight s ξ • fourierFun v ξ) =
        ⇑(𝓕 (SobolevSpace.bessel s v) : Lp F 2 (volume : Measure E)) := by
      funext ξ; exact weight_smul_fourierFun v ξ
    rw [this]; exact Lp.memLp _
  · rintro ⟨g, hg, hφ⟩
    rw [memSobolev_iff_exists_smulLeftCLM_fourier]
    refine ⟨hg.toLp _, ?_⟩
    ext φ
    rw [smulLeftCLM_apply_apply, hφ, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with ξ hξ
    erw [SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth s)]
    rw [hξ]
    simp only [smul_smul, smul_eq_mul, mul_comm]
end GroundTheory.Automorphic.Sobolev
