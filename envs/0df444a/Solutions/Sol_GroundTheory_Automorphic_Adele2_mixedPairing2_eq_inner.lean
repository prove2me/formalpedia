-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedPairing2_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:22:26.898259+00:00
-- url     : https://prove2.me/submissions/2943d468-72fc-4e64-b224-8c39a4ca1252

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_toEuclid2_apply
import Theorems.Thm_GroundTheory_Automorphic_Adele2_toEuclid2Conj_apply
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_eq_inner


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
namespace GroundTheory.Automorphic.Adele2
theorem _root_.solution (x y : Fin 2 → mixedSpace K) :
    mixedPairing2 K x y = ⟪toEuclid2 K x, toEuclid2Conj K y⟫ := by
  rw [mixedPairing2, Fin.sum_univ_two, toEuclid2_apply, toEuclid2Conj_apply,
    WithLp.prod_inner_apply, mixedTraceForm_eq_inner, mixedTraceForm_eq_inner]
end GroundTheory.Automorphic.Adele2
