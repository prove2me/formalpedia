-- Prove2me | solution 1 for GlobalTheory.WittSolve.inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:06.0218+00:00
-- url     : https://prove2.me/submissions/41b147e7-ea8d-4f15-bb5a-f498cc9886ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
import Theorems.Thm_GlobalTheory_WittSolve_smod_iff
import Theorems.Thm_GlobalTheory_WittSolve_inj_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittSolve
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type} [Fintype ι]
variable {M : Matrix ι ι (WittVector p R)}
namespace GlobalTheory.WittSolve
theorem _root_.solution
    (hU : ∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec
      (fun k => frobenius R p (x k)) = c)
    (v : ι → WittVector p R) (hv : F M v = 0) : v = 0 := by
  have key : ∀ n : ℕ, ∀ v : ι → WittVector p R, F M v = 0 → ∀ k, (p : WittVector p R) ^ n ∣ v k := by
    intro n
    induction n with
    | zero => intro v _ k; simp
    | succ n ih =>
      intro v hv k
      obtain ⟨w, rfl, hw⟩ := inj_step hU v hv
      simp only [Pi.smul_apply, smul_eq_mul, pow_succ']
      exact mul_dvd_mul_left _ (ih w hw k)
  funext k
  refine IsHausdorff.haus (I := Ideal.span {(p : WittVector p R)}) inferInstance (v k) fun n => ?_
  rw [smod_iff, sub_zero]
  exact key n v hv k
end GlobalTheory.WittSolve
