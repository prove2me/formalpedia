-- Prove2me | solution 1 for N4Code.Equivalent_normalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:27.634746+00:00
-- url     : https://prove2.me/submissions/37d156d8-737c-49ce-9b9f-98bdbf1567ff

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
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4) :
    Equivalent C (normalizeCode C i j) := by
  refine ⟨(permEven i j).symm, Equiv.refl (Fin n), fun t => (row C i) t, ?_⟩
  intro t
  rfl
end N4Code
