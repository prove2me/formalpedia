-- Prove2me | solution 1 for LinearSetReconciliation327.Main.cr23_upBlkSem_bw0
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-21T14:18:31.789512+00:00
-- url     : https://prove2.me/submissions/c352ddcb-0be6-4797-ad46-6c1f4bd29add

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23UpBlk

set_option autoImplicit false

open LinearSetReconciliation327.Main in
theorem solution (W N t : ℕ) (hW : 0 < W) (hN : 1 ≤ N) (ht : 1 ≤ t)
    (htN : t ≤ N) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (T : ℝ) :
    ¬ UpBlkSem progUpStmt (zeroDet W) T (cr23Sketch N t C) :=
  cr23_upBlkSem_bw0_false W N t hW hN ht htN C T
