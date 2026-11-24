-- Prove2me | solution 1 for GlobalTheory.WittSolve.modp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:46.820573+00:00
-- url     : https://prove2.me/submissions/0aa98333-96f9-49f5-af72-796185b7978a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
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
    (d : ι → WittVector p R) :
    ∃ u e : ι → WittVector p R, d = F M u + (p : WittVector p R) • e := by
  obtain ⟨x, hx, -⟩ := hU (fun k => WittVector.constantCoeff (d k))
  set u : ι → WittVector p R := fun k => WittVector.teichmuller p (x k) with hu
  have hc : (fun j => WittVector.constantCoeff (u j)) = x := by
    funext j; simp [hu, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  have hd : ∀ k, ∃ e, d k - F M u k = (p : WittVector p R) * e := by
    intro k
    apply (p_dvd_iff _).2
    have hc' : ∀ j, WittVector.constantCoeff (u j) = x j := fun j => congrFun hc j
    rw [map_sub, constantCoeff_F]
    simp only [hc']
    rw [hx, sub_self]
  choose e he using hd
  refine ⟨u, e, funext fun k => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← he k, add_sub_cancel]
end GlobalTheory.WittSolve
