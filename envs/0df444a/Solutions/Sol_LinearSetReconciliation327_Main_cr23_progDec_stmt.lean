-- Prove2me | solution 1 for LinearSetReconciliation327.Main.cr23_progDec_stmt
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-21T12:02:44.863011+00:00
-- url     : https://prove2.me/submissions/49443de1-0ee1-49b2-a834-4b505f59d5c4

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23Dec

set_option autoImplicit false

/-! Proposition 2.3's decoder is a compiled `Stmt`: `decStmt`.  The witness is the very statement
the development defines `progDec` from, so the existential closes by `rfl`. -/

open LinearSetReconciliation327.Main in
theorem solution : ∃ (Sdec : Stmt), Sdec.compile 0 ++ [iHalt] = progDec :=
  ⟨decStmt, rfl⟩
