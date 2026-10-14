-- Prove2me | solution 1 for L0BnB.BigMvsPR.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:19:47.614271+00:00
-- url     : https://prove2.me/submissions/32c7d06f-1d4c-4f97-84d5-84476645258e

import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_BigMvsPR_Relaxations
import Theorems.Thm_L0BnB_BigMvsPR_ineq_10
import Theorems.Thm_L0BnB_BigMvsPR_ineq_41
import Mathlib

open L0BnB.BigMvsPR L0BnB.Strength L0BnB.Reduced

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M) :
    (M ≤ (1 / 2) * Real.sqrt (lam0 / lam2) → L0BnB.Strength.VPRinf X y lam0 lam2 ≤ L0BnB.Strength.VB X y lam0 lam2 M) ∧
      (Real.sqrt (lam0 / lam2) ≤ M → lam2 ∈ L X y lam0 M →
        L0BnB.Strength.VB X y lam0 lam2 M ≤ L0BnB.Strength.VPRinf X y lam0 lam2) := by
  constructor
  · exact ineq_10 X y lam0 lam2 M hlam0 hlam2 hM
  · rintro hlarge ⟨_, β, hβ, hbox⟩
    have hleast : IsLeast (G X y lam0 lam2 '' Set.univ) (G X y lam0 lam2 β) := by
      refine ⟨⟨β, Set.mem_univ _, rfl⟩, ?_⟩
      rintro _ ⟨β', _, rfl⟩
      exact hβ β'
    have hval : VPRinf X y lam0 lam2 = G X y lam0 lam2 β := hleast.csInf_eq
    have hbdd : BddBelow (G X y lam0 lam2 '' box p M) := by
      refine ⟨G X y lam0 lam2 β, ?_⟩
      rintro _ ⟨β', _, rfl⟩
      exact hβ β'
    rw [hval]
    apply (ineq_41 X y lam0 lam2 M hlam0 hlam2 hM hlarge).trans
    exact csInf_le hbdd ⟨β, hbox, rfl⟩
