-- Prove2me | solution 1 for GeneralCK.finiteHybridBellman
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T23:06:11.866783+00:00
-- url     : https://prove2.me/submissions/6c13667a-5178-4d0e-ae8b-e7d1e1d85f23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GeneralCK_ArchiveRegionalBoundary_Inputs_toFiniteHybridBellman
import Theorems.Thm_GeneralCK_ArchiveRegionalBoundary_canonicalSameSide
import Theorems.Thm_GeneralCK_ArchiveRegionalBoundary_canonicalOppositeSide

theorem solution : GeneralCK.FiniteHybridBellman :=
  GeneralCK.ArchiveRegionalBoundary.Inputs.toFiniteHybridBellman
    ⟨GeneralCK.ArchiveRegionalBoundary.canonicalSameSide,
     GeneralCK.ArchiveRegionalBoundary.canonicalOppositeSide⟩
