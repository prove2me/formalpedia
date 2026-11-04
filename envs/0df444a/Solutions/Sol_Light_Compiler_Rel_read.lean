-- Prove2me | solution 1 for Light.Compiler.Rel.read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:47.920661+00:00
-- url     : https://prove2.me/submissions/15bfd5f0-f543-4fc8-ba71-4497abfaae4d

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}
namespace Light.Compiler
namespace Rel
theorem _root_.solution (R : Rel Z σ q m) {a : ℤ} (ha : Z.lim.Addr a) : m a = wd W (σ.mem a.toNat) := by
  have := R.mem a.toNat (by have := ha.1; have := ha.2; omega)
  rwa [Int.toNat_of_nonneg ha.1] at this
end Rel
end Light.Compiler
