-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.idealLatticePi_summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:09:36.959315+00:00
-- url     : https://prove2.me/submissions/9fda8e59-aa8d-4e6b-863e-7716e24d7ba3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Global_summable_norm_comp_add


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
theorem _root_.solution (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(ι → mixedSpace K, ℂ)) (a : ι → mixedSpace K) :
    Summable fun α : idealLatticePi I ↦ ‖f (α + a)‖ := by
  simpa [add_comm] using summable_norm_comp_add (idealLatticePi I) f a
end GroundTheory.Automorphic.GJMatrix
