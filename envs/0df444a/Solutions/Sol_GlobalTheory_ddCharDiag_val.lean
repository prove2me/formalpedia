-- Prove2me | solution 1 for GlobalTheory.ddCharDiag_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:23.519465+00:00
-- url     : https://prove2.me/submissions/a4ad0992-1e37-45ee-91ee-ab21386a30d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]
namespace GlobalTheory
theorem _root_.solution (d : n → Rˣ) :
    ((ddCharDiag d : GL n R) : Matrix n n R) = diagonal fun i => (d i : R) := rfl
end GlobalTheory
