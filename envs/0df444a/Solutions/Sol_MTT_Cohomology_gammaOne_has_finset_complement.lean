-- Prove2me | solution 1 for MTT.Cohomology.gammaOne_has_finset_complement
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-08T06:28:27.487545+00:00
-- url     : https://prove2.me/submissions/aa6d2876-a5e4-4611-a5ba-4f20d13f1d4a

import Definitions.Def_MTT_PeriodPairing

set_option autoImplicit false
noncomputable section

open MTT.Cohomology

theorem solution
    {N : ℕ} (hN : 0 < N) :
    ∃ R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      Subgroup.IsComplement
        (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨T, hT, -⟩ :=
    (CongruenceSubgroup.Gamma1 N).exists_isComplement_right 1
  have hTfinite : T.Finite := hT.finite_right
  exact ⟨hTfinite.toFinset, by simpa using hT⟩
