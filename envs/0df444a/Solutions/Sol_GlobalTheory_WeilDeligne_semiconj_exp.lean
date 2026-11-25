-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.semiconj_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:21:02.701682+00:00
-- url     : https://prove2.me/submissions/717d6294-cec3-4818-962e-6cb198b48275

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
open IsNilpotent
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {R : Type*} [Ring R] [Algebra ℚ R] {x a b : R} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (hx : x * a = b * x) : x * exp a = exp b * x := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨k, hk⟩ := hb
  rw [exp_eq_sum (pow_eq_zero_of_le (le_max_left m k) hm),
    exp_eq_sum (pow_eq_zero_of_le (le_max_right m k) hk), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, (SemiconjBy.pow_right (a := x) hx i).eq]
end GlobalTheory.WeilDeligne
