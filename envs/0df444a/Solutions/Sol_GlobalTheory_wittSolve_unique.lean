-- Prove2me | solution 1 for GlobalTheory.wittSolve_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:33.092884+00:00
-- url     : https://prove2.me/submissions/9365ffe3-80ba-4add-93df-43c7be3bbb49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
import Theorems.Thm_GlobalTheory_WittSolve_F_sub
import Theorems.Thm_GlobalTheory_WittSolve_inj
import Theorems.Thm_GlobalTheory_WittSolve_exists_sol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)),
    (∀ c : ι → R, ∃! x : ι → R,
      x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) →
    ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R,
      v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by
  intro p _ R _ _ _ ι _ M hU c
  obtain ⟨v, hv⟩ := WittSolve.exists_sol hU c
  refine ⟨v, hv, fun y hy => ?_⟩
  have h : WittSolve.F M (y - v) = 0 := by
    rw [WittSolve.F_sub]
    exact sub_eq_zero.2 (hy.trans hv.symm)
  exact sub_eq_zero.1 (WittSolve.inj hU _ h)
end GlobalTheory
