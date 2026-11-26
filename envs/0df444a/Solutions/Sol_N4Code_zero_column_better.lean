-- Prove2me | solution 1 for N4Code.zero_column_better
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:54.52225+00:00
-- url     : https://prove2.me/submissions/2cfc2de4-667a-4c30-af1a-298a474b4c62

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_g0_involutive
import Theorems.Thm_N4Code_zero_closer
import Theorems.Thm_N4Code_zero_equal_off
import Theorems.Thm_N4Code_compare_bij
import Theorems.Thm_N4Code_compare_bij_eq
import Theorems.Thm_N4Code_compare_bij_strict


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hcol : C t = col0) (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) :
    UniversalBetter (replaceColumn C t s') C ∧
      (UniversalEqual (replaceColumn C t s') C ↔ ∀ y : Word n, ¬ Y3c C s' hO hP t y) := by
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
  constructor
  · exact compare_bij C (replaceColumn C t s') S g hgt heq
  · constructor
    · intro heq2 y hS
      have hne : ∃ y : Word n, y ∈ S := ⟨y, Finset.mem_filter.mpr ⟨by simp, hS⟩⟩
      have hstrict := compare_bij_strict C (replaceColumn C t s') S g hgt heq hne
      have hgt' : lambda (replaceColumn C t s') (1 / 4 : ℝ) > lambda C (1 / 4) :=
        hstrict (1 / 4) (by norm_num) (by norm_num)
      have heq' : lambda (replaceColumn C t s') (1 / 4 : ℝ) = lambda C (1 / 4) :=
        heq2 (1 / 4) (by norm_num) (by norm_num)
      exact (lt_irrefl _ (hgt'.trans_eq heq')).elim
    · intro hy3
      have heqall : ∀ y : Word n, dCode C y = dCode (replaceColumn C t s') (g y) := by
        intro y
        by_cases hy : y ∈ S
        · exfalso
          exact hy3 y (Finset.mem_filter.mp hy).2
        · exact heq y hy
      exact compare_bij_eq C (replaceColumn C t s') g heqall
end N4Code
