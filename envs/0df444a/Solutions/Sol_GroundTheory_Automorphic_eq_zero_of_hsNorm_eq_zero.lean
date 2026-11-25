-- Prove2me | solution 1 for GroundTheory.Automorphic.eq_zero_of_hsNorm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:25:11.494215+00:00
-- url     : https://prove2.me/submissions/42791c1f-6439-4541-93ef-2243698ed003

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Theorems.Thm_GroundTheory_Automorphic_eq_zero_of_hsNormSq_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace GroundTheory.Automorphic
theorem _root_.solution {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (h : hsNorm T = 0) :
    T = 0 := by
  refine eq_zero_of_hsNormSq_eq_zero ?_
  rw [hsNorm, Real.sqrt_eq_zero ENNReal.toReal_nonneg, ENNReal.toReal_eq_zero_iff] at h
  exact h.resolve_right hT.ne
end GroundTheory.Automorphic
