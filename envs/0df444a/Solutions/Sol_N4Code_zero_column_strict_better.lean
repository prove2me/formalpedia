-- Prove2me | solution 1 for N4Code.zero_column_strict_better
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:17.601907+00:00
-- url     : https://prove2.me/submissions/6eb50a11-1e0e-48b7-89d2-2966666d495a

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_g0_involutive
import Theorems.Thm_N4Code_zero_closer
import Theorems.Thm_N4Code_zero_equal_off
import Theorems.Thm_N4Code_compare_bij_strict


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hcol : C t = col0) (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty)
    (hy : ∃ y : Word n, Y3c C s' hO hP t y) :
    UniversalStrictBetter (replaceColumn C t s') C := by
  let S : Finset (Word n) := Finset.univ.filter (Y3c C s' hO hP t)
  have hbij : Function.Bijective (g0 C s' hO hP t) := by
    constructor
    · intro a b hab
      calc
        a = g0 C s' hO hP t (g0 C s' hO hP t a) := (g0_involutive C s' hO hP t a hcol).symm
        _ = g0 C s' hO hP t (g0 C s' hO hP t b) := by rw [hab]
        _ = b := g0_involutive C s' hO hP t b hcol
    · intro z
      refine ⟨g0 C s' hO hP t z, ?_⟩
      exact g0_involutive C s' hO hP t z hcol
  let g : Word n ≃ Word n := Equiv.ofBijective (g0 C s' hO hP t) hbij
  have hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode (replaceColumn C t s') (g y) := by
    intro y hy
    have hS : Y3c C s' hO hP t y := (Finset.mem_filter.mp hy).2
    have h := zero_closer C t s' hcol hO hP y hS
    have hlt : dCode (replaceColumn C t s') (g0 C s' hO hP t y) < dCode C y := by
      rw [h]
      omega
    simpa [g] using hlt
  have heq : ∀ y : Word n, y ∉ S → dCode C y = dCode (replaceColumn C t s') (g y) := by
    intro y hy
    have hnot : ¬ Y3c C s' hO hP t y := by
      intro h
      exact hy (Finset.mem_filter.mpr ⟨by simp, h⟩)
    simpa [g] using zero_equal_off C t s' hcol hO hP y hnot
  have hne : ∃ y : Word n, y ∈ S := by
    rcases hy with ⟨y, hy⟩
    exact ⟨y, Finset.mem_filter.mpr ⟨by simp, hy⟩⟩
  exact compare_bij_strict C (replaceColumn C t s') S g hgt heq hne
end N4Code
