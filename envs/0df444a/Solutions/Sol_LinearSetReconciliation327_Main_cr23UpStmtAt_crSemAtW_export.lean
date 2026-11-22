-- Prove2me | solution 1 for LinearSetReconciliation327.Main.cr23UpStmtAt_crSemAtW_export
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-21T14:51:14.709596+00:00
-- url     : https://prove2.me/submissions/2d7b52ff-29df-4468-a205-9f02eb6e1d10

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23UpAt

set_option autoImplicit false

open LinearSetReconciliation327.Main in
theorem solution (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t))
    (E : RAMEnv) (hEW : E.W = cr23Word N) (Bw : ℕ) (hBw : cr23Graph0 N ≤ Bw) :
    CrSemAtW cr23UpStmtAt E (65536 * lg ((N : ℝ) + 2) ^ 2) Bw N t C :=
  cr23UpStmtAt_crSemAtW N t hN htN C E hEW Bw hBw
