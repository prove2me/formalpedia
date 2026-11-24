-- Prove2me | solution 1 for GlobalTheory.DetClass.det_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:11:03.836211+00:00
-- url     : https://prove2.me/submissions/0fa3b800-c62e-4465-9425-9b9253a6e2cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.DetClass
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.DetClass
theorem _root_.solution {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (a b : (i : ι) → I i) :
    (∏ i, (b i : R)) * (mat φ a).det = (∏ i, (a i : R)) * (mat φ b).det := by
  have key : mat φ a * Matrix.diagonal (fun i => (b i : R))
      = mat φ b * Matrix.diagonal (fun i => (a i : R)) := by
    ext j i
    simp only [Matrix.mul_diagonal, mat]
    have h1 : (b i : R) • (Pi.single i (a i) : (k : ι) → I k)
        = (a i : R) • (Pi.single i (b i) : (k : ι) → I k) := by
      funext k
      by_cases hk : k = i
      · subst hk
        apply Subtype.ext
        simp [mul_comm]
      · simp [Pi.single_eq_of_ne hk]
    have h2 := congrArg (fun x => ((φ x) j : R)) h1
    simp only [map_smul, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul] at h2
    rw [mul_comm, h2, mul_comm]
  have h := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at h
  rw [mul_comm, h, mul_comm]
end GlobalTheory.DetClass
