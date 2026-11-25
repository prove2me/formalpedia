-- Prove2me | solution 1 for GroundTheory.Automorphic.CuspidalSpectrum.exists_pos_natCast_mul_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:48.756685+00:00
-- url     : https://prove2.me/submissions/0af2c878-461d-4d0b-aec9-5f5a1ddbde0b

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
namespace GroundTheory.Automorphic.CuspidalSpectrum
theorem _root_.solution (k : K) : ∃ c : ℕ, 0 < c ∧ IsIntegral ℤ ((c : K) * k) := by
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic k))
  obtain ⟨c, hc | hc⟩ := Int.eq_nat_or_neg y
  · refine ⟨c, Nat.pos_of_ne_zero fun h => hy0 (by rw [hc, h, Nat.cast_zero]), ?_⟩
    have : (c : K) * k = y • k := by rw [zsmul_eq_mul, hc]; push_cast; ring
    rw [this]
    exact hyint
  · refine ⟨c, Nat.pos_of_ne_zero fun h => hy0 (by rw [hc, h, Nat.cast_zero, neg_zero]), ?_⟩
    have : (c : K) * k = -(y • k) := by rw [zsmul_eq_mul, hc]; push_cast; ring
    rw [this]
    exact hyint.neg
end GroundTheory.Automorphic.CuspidalSpectrum
