-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.dualIdealLattice2_summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:54:19.015449+00:00
-- url     : https://prove2.me/submissions/05d03eb2-f944-42e2-ae77-de3a933e2847

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourier2Schwartz_apply
import Theorems.Thm_GroundTheory_Global_summable_norm_comp_add


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
theorem _root_.solution (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) (a : Fin 2 → mixedSpace K) :
    Summable fun β : idealLattice2 (fun i => traceDualIdeal K (I i)) =>
      ‖mixedFourier2 K f β * 𝐞 (mixedPairing2 K β a)‖ := by
  have h := summable_norm_comp_add (idealLattice2 (fun i => traceDualIdeal K (I i)))
    (mixedFourier2Schwartz K f) 0
  simp only [zero_add, mixedFourier2Schwartz_apply] at h
  simpa only [norm_mul, Circle.norm_coe, mul_one] using h
end GroundTheory.Automorphic.Adele2
