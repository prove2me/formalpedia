-- Prove2me | solution 1 for GroundTheory.Automorphic.CuspidalSpectrum.exists_abs_repr_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:48.140135+00:00
-- url     : https://prove2.me/submissions/83add6dd-15f7-4e3b-a729-cc56b6a13dfe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Set
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.CuspidalSpectrum
variable (K : Type*) [Field K] [NumberField K]
open scoped Classical
namespace GroundTheory.Automorphic.CuspidalSpectrum
theorem _root_.solution :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : 𝓞 K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)),
      |(((RingOfIntegers.basis K).repr z i : ℤ) : ℝ)| ≤
        C * ‖mixedEmbedding K (z : K)‖ := by
  set Lc := LinearMap.toContinuousLinearMap (mixedEmbedding.latticeBasis K).equivFun.toLinearMap
  refine ⟨‖Lc‖, norm_nonneg _, fun z i => ?_⟩
  have hval : Lc (mixedEmbedding K (z : K)) i = (((RingOfIntegers.basis K).repr z i : ℤ) : ℝ) := by
    change (mixedEmbedding.latticeBasis K).equivFun (mixedEmbedding K (z : K)) i = _
    rw [Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply]
    have := integralBasis_repr_apply K z i
    rw [show (z : K) = algebraMap (𝓞 K) K z from rfl, this]
    simp
  rw [← hval, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ i).trans (Lc.le_opNorm _)
end GroundTheory.Automorphic.CuspidalSpectrum
