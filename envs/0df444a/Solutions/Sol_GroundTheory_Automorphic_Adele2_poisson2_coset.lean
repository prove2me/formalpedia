-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.poisson2_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:24.871244+00:00
-- url     : https://prove2.me/submissions/91bf7217-9d47-4881-9b54-ad238714fd1a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_idealLattice2_summable_norm
import Theorems.Thm_GroundTheory_Automorphic_Adele2_dualIdealLattice2_summable_norm
import Theorems.Thm_GroundTheory_Automorphic_Adele2_idealLattice2_poisson_summation
import Theorems.Thm_GroundTheory_Automorphic_Adele2_emb2_zero
import Theorems.Thm_GroundTheory_Automorphic_Adele2_summable_norm_iff_and_tsum_eq_coset2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Automorphic.Adele2
theorem _root_.solution (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : Fin 2 → K)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) :
    Summable (fun ξ : Fin 2 → K => ‖(coset2 K I c).indicator (fun ξ => f (emb2 K ξ)) ξ‖) ∧
    Summable (fun η : Fin 2 → K => ‖(coset2 K (fun i => traceDualIdeal K (I i)) 0).indicator
      (fun η => mixedFourier2 K f (emb2 K η) *
        (𝐞 (mixedPairing2 K (emb2 K η) (emb2 K c)) : ℂ)) η‖) ∧
    ∑' ξ : Fin 2 → K, (coset2 K I c).indicator (fun ξ => f (emb2 K ξ)) ξ =
      (((∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ : ℝ) : ℂ) *
        ∑' η : Fin 2 → K, (coset2 K (fun i => traceDualIdeal K (I i)) 0).indicator
          (fun η => mixedFourier2 K f (emb2 K η) *
            (𝐞 (mixedPairing2 K (emb2 K η) (emb2 K c)) : ℂ)) η := by
  have hL := summable_norm_iff_and_tsum_eq_coset2 I c f
  have hR := summable_norm_iff_and_tsum_eq_coset2 (fun i => traceDualIdeal K (I i)) 0
    (fun v => mixedFourier2 K f v * (𝐞 (mixedPairing2 K v (emb2 K c)) : ℂ))
  simp only [emb2_zero, add_zero] at hR
  refine ⟨hL.1.mpr (idealLattice2_summable_norm I f (emb2 K c)),
    hR.1.mpr (dualIdealLattice2_summable_norm I f (emb2 K c)), ?_⟩
  rw [hL.2, hR.2, idealLattice2_poisson_summation, Complex.real_smul]
end GroundTheory.Automorphic.Adele2
