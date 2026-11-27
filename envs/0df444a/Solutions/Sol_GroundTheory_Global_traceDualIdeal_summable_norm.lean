-- Prove2me | solution 1 for GroundTheory.Global.traceDualIdeal_summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:44.691253+00:00
-- url     : https://prove2.me/submissions/f81f4077-d55a-4fe1-98d7-9fb89ee2b98a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Theorems.Thm_GroundTheory_Global_mixedFourierSchwartz_apply
import Theorems.Thm_GroundTheory_Global_summable_norm_comp_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace FourierTransform SchwartzMap nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) :
    Summable fun β : idealLattice K (traceDualIdeal K I) =>
      ‖mixedFourier K f β * 𝐞 (mixedTraceForm K β a)‖ := by
  have h := summable_norm_comp_add (idealLattice K (traceDualIdeal K I)) (mixedFourierSchwartz K f) 0
  simpa [norm_mul, Circle.norm_coe, mixedFourierSchwartz_apply] using h
end GroundTheory.Global
