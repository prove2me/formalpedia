-- Prove2me | solution 1 for LinearSetReconciliation327.Main.pinsketch_decoder_key_solver_bounded
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-22T05:49:38.82579+00:00
-- url     : https://prove2.me/submissions/b8f80335-9d10-4764-99a1-8d1d05b99b94

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_P21BndKey20261122

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open scoped ENNReal
open Finset

open LinearSetReconciliation327.Main in
/-- The bounded key solver, submission wrapper matching the target statement. -/
theorem solution {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (P : Program) (E : RAMEnv) (pc : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile keySolverProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : E.det = detStd t N b ι) (ht : 1 ≤ t)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (h0 : ι 0 ≠ 0)
    (hh0 : E.det 0 % 2 ^ E.W = t) (hh1 : E.det 1 % 2 ^ E.W = w) (hh2 : E.det 2 % 2 ^ E.W = N)
    (hSaved : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m addr = 0) :
    Sem P E pc (pc + 960) (boundaryState pc m)
      (fun k z => k ≤ (34 * decoderCapacity t + (48 * decoderLength t + 187) * decoderLength t + 289) * decoderLength t +
          12 * decoderCapacity t + 385 ∧ ∃ m', z = boundaryState (pc + 960) m' ∧
        KeyReady b E t N e m' ∧
        MemoryFrame (solverInitWritable t) m m') :=
  LinearSetReconciliation327.Main.P21Bnd.pinsketch_decoder_key_solverB b ι t N P E pc e m hAt hw hW hdet ht hEnd h0 hh0 hh1 hh2 hSaved hTail
