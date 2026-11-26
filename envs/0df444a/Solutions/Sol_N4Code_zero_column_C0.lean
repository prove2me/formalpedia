-- Prove2me | solution 1 for N4Code.zero_column_C0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:33.599839+00:00
-- url     : https://prove2.me/submissions/6d44a921-d049-49fb-addb-1b4bd8ffde7a

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_zero_column_better
import Theorems.Thm_N4Code_y3c_empty_C0
import Theorems.Thm_N4Code_rowPermute_refl
import Theorems.Thm_N4Code_universalEqual_of_equivalent


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (h0 : C t = col0)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h5 : Odd (count C 5)) (h6 : Odd (count C 6)) :
    ∀ s' : Column, UniversalEqual (replaceColumn C t s') C := by
  intro s'
  by_cases hs0 : s' = col0
  · subst s'
    exact universalEqual_of_equivalent C (replaceColumn C t col0) (by
      have hrep : replaceColumn C t col0 = C := by
        funext u
        by_cases hu : u = t <;> simp [replaceColumn, hu, h0]
      rw [hrep]
      refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun _ => false, ?_⟩
      intro u
      simp [rowPermute_refl])
  · by_cases hs15 : s' = col15
    · subst s'
      exact universalEqual_of_equivalent C (replaceColumn C t col15) (by
        refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun u => u = t, ?_⟩
        intro u
        by_cases hu : u = t
        · subst u
          have hflip : flipCol col0 = col15 := by
            funext k
            simp [flipCol, col15, col0]
          simp [h0, hflip, rowPermute_refl, replaceColumn]
        · simp [hu, replaceColumn, rowPermute_refl])
    · have hO : (colZeros s').Nonempty := by
        rw [Finset.Nonempty]
        by_contra h
        have : s' = col15 := by
          funext k
          by_contra hk
          have hfalse : s' k = false := by
            cases hs : s' k
            · rfl
            · exact (hk hs).elim
          exfalso
          exact h ⟨k, by simp [colZeros, hfalse]⟩
        exact hs15 this
      have hP : (colOnes s').Nonempty := by
        rw [Finset.Nonempty]
        by_contra h
        have : s' = col0 := by
          funext k
          by_contra hk
          have htrue : s' k = true := by
            cases hs : s' k
            · exact (hk hs).elim
            · rfl
          exfalso
          exact h ⟨k, by simp [colOnes, htrue]⟩
        exact hs0 this
      have hb := zero_column_better C t s' h0 hO hP
      exact hb.2.mpr (y3c_empty_C0 C t s' hO hP hC h5 h6)
end N4Code
