-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.zeta_six
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:26:33.758492+00:00
-- url     : https://prove2.me/submissions/ec8949ff-0389-4d72-83f7-8ebbda761c4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
open GlobalTheory GlobalTheory.DiscUniformisation
namespace GlobalTheory.DiscUniformisation
theorem _root_.solution : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h6 : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    simp [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
      bernoulli'_four, h5, Nat.choose]
    norm_num
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  rw [show (2 : ℂ) * ((3 : ℕ) : ℂ) = 6 by norm_num, h6] at h
  rw [h]
  norm_num [Nat.factorial]
  ring
end GlobalTheory.DiscUniformisation
