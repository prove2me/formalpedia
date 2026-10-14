-- Prove2me | solution 1 for L0BnB.BigMvsPR.ineq_41
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:15:14.116429+00:00
-- url     : https://prove2.me/submissions/d3dba160-5956-47bb-8737-f4f64bdd7693

import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_BigMvsPR_Relaxations
import Theorems.Thm_L0BnB_BigMvsPR_eq_37
import Theorems.Thm_L0BnB_BigMvsPR_lemma_1
import Mathlib

open L0BnB.BigMvsPR L0BnB.Strength L0BnB.Reduced

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hMlarge : Real.sqrt (lam0 / lam2) ≤ M) :
    L0BnB.Strength.VB X y lam0 lam2 M ≤ vStar X y lam0 lam2 M := by
  classical
  apply le_csInf
  · refine ⟨G X y lam0 lam2 0, 0, ?_, rfl⟩
    simpa [box] using fun _ : Fin p => hM.le
  · rintro v ⟨β, hβ, rfl⟩
    apply ((eq_37 X y lam0 lam2 M hlam0 hlam2 hM).2 ⟨β, hβ, rfl⟩).trans
    unfold H G
    gcongr with i
    have hi := (abs_le.mp (hβ i))
    have ht := lemma_1 lam0 lam2 M hlam0 hlam2 hM hMlarge (β i) hi.1 hi.2
    unfold tGap psi1 at *
    linarith
