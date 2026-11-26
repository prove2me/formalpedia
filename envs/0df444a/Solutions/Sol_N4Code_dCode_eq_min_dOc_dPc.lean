-- Prove2me | solution 1 for N4Code.dCode_eq_min_dOc_dPc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:49.955283+00:00
-- url     : https://prove2.me/submissions/928c66e0-e26b-45a2-aa98-d1c1e7907271

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRowMin_union
import Theorems.Thm_N4Code_dRowMin_univ

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (y : Word n) :
    dCode C y = min (dOc C s' hO y) (dPc C s' hP y) := by
  have hunion : (Finset.univ : Finset (Fin 4)) = colZeros s' ∪ colOnes s' := by
    ext i
    simp [colZeros, colOnes]
  calc
    dCode C y = dRowMin C (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty y :=
      (dRowMin_univ C y).symm
    _ = dRowMin C (colZeros s' ∪ colOnes s')
        (by rcases hO with ⟨i, hi⟩; exact ⟨i, Finset.mem_union_left (colOnes s') hi⟩) y := by
          simp [hunion]
    _ = min (dRowMin C (colZeros s') hO y) (dRowMin C (colOnes s') hP y) := by
          simpa using dRowMin_union C (colZeros s') (colOnes s') hO hP y
    _ = min (dOc C s' hO y) (dPc C s' hP y) := by rfl
end N4Code
