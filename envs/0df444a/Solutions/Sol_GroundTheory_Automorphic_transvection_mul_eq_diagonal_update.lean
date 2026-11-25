-- Prove2me | solution 1 for GroundTheory.Automorphic.transvection_mul_eq_diagonal_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:44.77842+00:00
-- url     : https://prove2.me/submissions/c2178ded-8057-4719-8ef9-aa39eb24d686

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
import Theorems.Thm_GroundTheory_Automorphic_mul_transvection_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}
namespace GroundTheory.Automorphic
theorem _root_.solution (i j : n) (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-(↑u⁻¹ : R)) * transvection i j (u : R) *
      transvection i j (-1) * transvection j i 1 * transvection i j (-1) =
      diagonal (Function.update (Function.update (1 : n → R) i u) j (↑u⁻¹ : R)) := by
  ext a b
  simp only [mul_transvection_apply]
  simp only [diagonal_apply, Function.update_apply, Pi.one_apply, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hbj : b = j <;> by_cases hbi : b = i <;> by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp [hbj, hbi, hai, haj, hij, Ne.symm hij, @eq_comm _ i, @eq_comm _ j]
  all_goals (try ring_nf)
  all_goals (try simp)
end GroundTheory.Automorphic
