-- Prove2me | solution 1 for N4Code.dCode_replace_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:45.51823+00:00
-- url     : https://prove2.me/submissions/bf03e878-0386-41ca-8936-13105a9034b0

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRowMin_union
import Theorems.Thm_N4Code_dRowMin_univ
import Theorems.Thm_N4Code_dRow_replace_zero

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) (y : Word n) :
    dCode (replaceColumn C t s') y = min (dOc C s' hO y) (dPc C s' hP (flipBit t y)) := by
  let C' : Code n := replaceColumn C t s'
  have hunion : (Finset.univ : Finset (Fin 4)) = colZeros s' ∪ colOnes s' := by
    ext i
    simp [colZeros, colOnes]
  have hz : dRowMin C' (colZeros s') hO y = dRowMin C (colZeros s') hO y := by
    unfold dRowMin
    have hcong : (colZeros s').image (fun i => dRow C' i y) =
        (colZeros s').image (fun i => dRow C i y) := by
      apply Finset.image_congr
      intro i hi
      have hs' : ¬ s' i := (Finset.mem_filter.mp hi).2
      exact (dRow_replace_zero C t s' hcol y i).trans (by simp [hs'])
    simp [hcong]
  have hp : dRowMin C' (colOnes s') hP y = dRowMin C (colOnes s') hP (flipBit t y) := by
    unfold dRowMin
    have hcong : (colOnes s').image (fun i => dRow C' i y) =
        (colOnes s').image (fun i => dRow C i (flipBit t y)) := by
      apply Finset.image_congr
      intro i hi
      have hs' : s' i := (Finset.mem_filter.mp hi).2
      exact (dRow_replace_zero C t s' hcol y i).trans (by simp [hs'])
    simp [hcong]
  calc
    dCode C' y = dRowMin C' (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty y :=
      (dRowMin_univ C' y).symm
    _ = dRowMin C' (colZeros s' ∪ colOnes s')
        (by rcases hO with ⟨i, hi⟩; exact ⟨i, Finset.mem_union_left (colOnes s') hi⟩) y := by
          simp [hunion]
    _ = min (dRowMin C' (colZeros s') hO y) (dRowMin C' (colOnes s') hP y) := by
          simpa using dRowMin_union C' (colZeros s') (colOnes s') hO hP y
    _ = min (dOc C s' hO y) (dPc C s' hP (flipBit t y)) := by
          rw [hz, hp]
          rfl
end N4Code
