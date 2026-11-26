-- Prove2me | solution 1 for N4Code.dCode_replace_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:33.459218+00:00
-- url     : https://prove2.me/submissions/407cae77-f766-4152-a7cd-8aec1e4889ec

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dRow_replace_2
import Theorems.Thm_N4Code_dRow_replace_eq

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    dCode (replaceColumn C t col3) y = min (dO C y) (dPp C t y) := by
  unfold dCode dO dPp dP
  change min (dRow (replaceColumn C t col3) ⟨0, by decide⟩ y)
      (min (dRow (replaceColumn C t col3) ⟨1, by decide⟩ y)
        (min (dRow (replaceColumn C t col3) ⟨2, by decide⟩ y)
          (dRow (replaceColumn C t col3) ⟨3, by decide⟩ y))) =
    min (min (dRow C ⟨0, by decide⟩ y) (min (dRow C ⟨1, by decide⟩ y) (dRow C ⟨3, by decide⟩ y)))
      (dRow C ⟨2, by decide⟩ (flipBit t y))
  rw [dRow_replace_eq C t ⟨0, by decide⟩ y hcol (by decide),
    dRow_replace_eq C t ⟨1, by decide⟩ y hcol (by decide),
    dRow_replace_2 C t y hcol,
    dRow_replace_eq C t ⟨3, by decide⟩ y hcol (by decide)]
  omega
end N4Code
