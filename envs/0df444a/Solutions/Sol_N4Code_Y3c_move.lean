-- Prove2me | solution 1 for N4Code.Y3c_move
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:27.726504+00:00
-- url     : https://prove2.me/submissions/0a311fc8-0ffd-425b-930b-ea64421d72c0

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRowMin_swapBit

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t₁ t' : Fin n)
    (h1 : C t₁ = col0) (h' : C t' = col0) :
    (∃ y : Word n, Y3c C s' hO hP t' y) → (∃ y : Word n, Y3c C s' hO hP t₁ y) := by
  rintro ⟨y, hy⟩
  refine ⟨swapBits t₁ t' y, ?_⟩
  constructor
  · simpa [swapBits] using hy.1
  · have hdO := dRowMin_swapBit C (colZeros s') hO t₁ t' h1 h' y
    have hdP := dRowMin_swapBit C (colOnes s') hP t₁ t' h1 h' y
    unfold Y3c at hy
    unfold dOc dPc at hy ⊢
    rw [hdO, hdP]
    exact hy.2
end N4Code
