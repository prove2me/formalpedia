-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.poissonPi_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:04.105798+00:00
-- url     : https://prove2.me/submissions/0e88f342-55b1-42fc-beb1-e8caddb1b9df

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_idealLatticePi_summable_norm
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_dualIdealLatticePi_summable_norm
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_idealLatticePi_poisson_summation
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_embPi_zero
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_summable_norm_iff_and_tsum_eq_cosetPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
variable {K}
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ι → K)
    (f : 𝓢(ι → mixedSpace K, ℂ)) :
    Summable (fun ξ : ι → K ↦ ‖(cosetPi K I c).indicator (fun ξ ↦ f (embPi K ξ)) ξ‖) ∧
    Summable (fun η : ι → K ↦ ‖(cosetPi K (fun i ↦ traceDualIdeal K (I i)) 0).indicator
      (fun η ↦ mixedFourierPi K f (embPi K η) *
        (𝐞 (mixedPairingPi K (embPi K η) (embPi K c)) : ℂ)) η‖) ∧
    ∑' ξ : ι → K, (cosetPi K I c).indicator (fun ξ ↦ f (embPi K ξ)) ξ =
      (((∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ : ℝ) : ℂ) *
        ∑' η : ι → K, (cosetPi K (fun i ↦ traceDualIdeal K (I i)) 0).indicator
          (fun η ↦ mixedFourierPi K f (embPi K η) *
            (𝐞 (mixedPairingPi K (embPi K η) (embPi K c)) : ℂ)) η := by
  have hL := summable_norm_iff_and_tsum_eq_cosetPi I c f
  have hR := summable_norm_iff_and_tsum_eq_cosetPi (fun i ↦ traceDualIdeal K (I i)) 0
    (fun v ↦ mixedFourierPi K f v * (𝐞 (mixedPairingPi K v (embPi K c)) : ℂ))
  simp only [embPi_zero, add_zero] at hR
  refine ⟨hL.1.mpr (idealLatticePi_summable_norm I f (embPi K c)),
    hR.1.mpr (dualIdealLatticePi_summable_norm I f (embPi K c)), ?_⟩
  rw [hL.2, hR.2, idealLatticePi_poisson_summation, Complex.real_smul]
end GroundTheory.Automorphic.GJMatrix
