-- Prove2me | solution 1 for LawlerCompress.TardyJobs.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @0xbf
-- created : 2026-11-12T14:37:02.993239+00:00
-- url     : https://prove2.me/submissions/1add3b7a-873f-4fb6-a6f9-23c2efd5e8eb

import Theorems.Thm_LawlerCompress_TardyJobs_lemma_2_1_without_EDD

set_option autoImplicit false

open LawlerCompress.TardyJobs

theorem solution {m : ℕ} (hm : 1 ≤ m) (I : Instance m)
    (hn : 1 ≤ I.n) (hedd : EDD I) (j : Fin I.n) :
    I.p j ≤ a I j ∧ a I j ≤ I.d j + 1 ∧
    cbar I j = Finset.Icc (a I j) (I.d j) ∧
    (cbar I j = ∅ → a I j = I.d j + 1) := by
  exact LawlerCompress.TardyJobs.lemma_2_1_without_EDD I j
