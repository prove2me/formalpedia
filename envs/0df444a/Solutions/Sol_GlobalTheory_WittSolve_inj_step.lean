-- Prove2me | solution 1 for GlobalTheory.WittSolve.inj_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:46.020527+00:00
-- url     : https://prove2.me/submissions/d0628c68-012d-4810-a9be-8c6ccbf9c323

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
import Theorems.Thm_GlobalTheory_WittSolve_F_smul
import Theorems.Thm_GlobalTheory_WittSolve_constantCoeff_F
import Theorems.Thm_GlobalTheory_WittSolve_p_dvd_iff

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
    (v : ι → WittVector p R) (hv : F M v = 0) :
    ∃ w : ι → WittVector p R, v = (p : WittVector p R) • w ∧ F M w = 0 := by
  have hx : (fun j => WittVector.constantCoeff (v j)) - (M.map WittVector.constantCoeff).mulVec
      (fun j => frobenius R p (WittVector.constantCoeff (v j))) = 0 := by
    funext k
    rw [← constantCoeff_F, hv]; simp
  have h0 : (0 : ι → R) - (M.map WittVector.constantCoeff).mulVec
      (fun j => frobenius R p ((0 : ι → R) j)) = 0 := by
    simp only [Pi.zero_apply, map_zero, zero_sub, neg_eq_zero]
    exact Matrix.mulVec_zero _
  have hx0 := (hU 0).unique hx h0
  have hd : ∀ k, ∃ w, v k = (p : WittVector p R) * w := by
    intro k
    exact (p_dvd_iff (v k)).2 (congrFun hx0 k)
  choose w hw using hd
  refine ⟨w, funext fun k => by simp [hw k], ?_⟩
  have h1 : F M ((p : WittVector p R) ^ 1 • w) = 0 := by
    rw [pow_one]; convert hv; funext k; simp [hw k]
  rw [F_smul, pow_one] at h1
  funext k
  have := congrFun h1 k
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact WittVector.eq_zero_of_p_mul_eq_zero _ (by rw [mul_comm]; exact this)
end GlobalTheory.WittSolve
