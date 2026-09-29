-- Prove2me | solution 1 for MTT.Eigenform.heckeEigenvalue_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-18T21:20:37.446064+00:00
-- url     : https://prove2.me/submissions/28304ff0-667e-422d-ba8c-b3144535a6b2

import Theorems.Thm_MTT_Cohomology_eigenform_hecke_stable_period_lattice
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option autoImplicit false
noncomputable section

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (l : ℕ) (hl : l.Prime) :
    IsIntegral ℤ (f.coeff l) := by
  obtain ⟨ψ, _hpacket, hne, hfg, hstable⟩ :=
    MTT.Cohomology.eigenform_hecke_stable_period_lattice hN hk ι f l hl
  let L : Submodule ℤ MTT.Qbar :=
    Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
      v = MTT.Cohomology.evaluation j r (ψ s) /
        ((k - 2).choose j : MTT.Qbar)}
  exact isIntegral_of_smul_mem_submodule L hne hfg (f.coeff l) (by
    intro x hx
    simpa only [smul_eq_mul, L] using
      hstable x (by simpa only [L] using hx))
