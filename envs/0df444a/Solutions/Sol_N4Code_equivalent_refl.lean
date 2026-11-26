-- Prove2me | solution 1 for N4Code.equivalent_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:23.053839+00:00
-- url     : https://prove2.me/submissions/63d7eaa7-3460-4f04-897c-092fb71df337

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) : Equivalent C C := by
  refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun _ => false, ?_⟩
  intro t
  change C t = rowPermute (Equiv.refl (Fin 4)) (C t)
  ext j
  simp [rowPermute]
end N4Code
