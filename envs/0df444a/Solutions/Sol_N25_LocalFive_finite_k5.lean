-- Prove2me | solution 1 for N25.LocalFive.finite_k5
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:19.345915+00:00
-- url     : https://prove2.me/submissions/7808faad-e302-418e-b633-d14663a87c41

import Mathlib
import Definitions.Def_N25_LocalFiveArithmetic

noncomputable section

local instance instL_N25_LocalFive_finite_k5_bfd51b_s828a6f : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace N25.LocalFive

/-- The residue field of the 5-adic integers is finite. -/
theorem _root_.solution : Finite k5 :=
  Finite.of_injective (PadicInt.residueField (p := 5))
    (PadicInt.residueField (p := 5)).injective

end N25.LocalFive
