-- Prove2me | solution 1 for N4Code.zero_column_strict_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:39.373137+00:00
-- url     : https://prove2.me/submissions/71d9b679-771c-4f4e-acf1-1bd0d85799e6

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colVal_rowPermute_col5
import Theorems.Thm_N4Code_rowPermute_left_inv
import Theorems.Thm_N4Code_flipCol_rowPermute
import Theorems.Thm_N4Code_zero_column_strict_witness
import Theorems.Thm_N4Code_strict_better_two_bit_col0
import Theorems.Thm_N4Code_lambda_equiv


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (ρ : Equiv (Fin 4) (Fin 4))
    (f : Fin n → Bool) (hh : ∀ u : Fin n, C' u = rowPermute ρ (if f u then flipCol (C u) else C u))
    (t : Fin n) (hcolC : C t = col0) (hcolC' : C' t = col0)
    (h : ∃ y : Word n, Y3c C' col5 colZeros_col5_nonempty colOnes_col5_nonempty t y) :
    ∃ s' : Column, (colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) ∧
      UniversalStrictBetter (replaceColumn C t s') C := by
  have hStrict' : UniversalStrictBetter (replaceColumn C' t col5) C' :=
    zero_column_strict_witness C' t hcolC' h
  have hft : f t = false := by
    by_contra hf
    have hft' : f t = true := by
      cases hx : f t
      · exfalso
        exact hf hx
      · rfl
    have hh' := hh t
    rw [hcolC, hft'] at hh'
    simp at hh'
    have hc : C' t = col15 := by
      have hrow : rowPermute ρ (flipCol col0) = col15 := by
        funext k
        simp [rowPermute, flipCol, col0, col15]
      rwa [hrow] at hh'
    have h01 : col0 = col15 := hcolC'.symm.trans hc
    have hbad : (false : Bool) = true := congrFun h01 ⟨0, by decide⟩
    simp at hbad
  let s₀ : Column := rowPermute ρ.symm (if f t then flipCol col5 else col5)
  have hEqRep : Equivalent (replaceColumn C' t col5) (replaceColumn C t s₀) := by
    refine ⟨ρ.symm, Equiv.refl (Fin n), f, ?_⟩
    intro u
    by_cases hu : u = t
    · subst u
      simp [s₀, replaceColumn, hft]
    · have hmain : C u = rowPermute ρ.symm (if f u then flipCol (C' u) else C' u) := by
        by_cases hfu : f u
        · have hh' := hh u
          rw [hfu] at hh'
          simp at hh'
          have hrow : rowPermute ρ.symm (C' u) = flipCol (C u) := by
            rw [hh']
            exact rowPermute_left_inv ρ (flipCol (C u))
          calc
            C u = flipCol (flipCol (C u)) := by
              funext j
              simp [flipCol]
            _ = flipCol (rowPermute ρ.symm (C' u)) := by rw [← hrow]
            _ = rowPermute ρ.symm (flipCol (C' u)) := by rw [flipCol_rowPermute ρ.symm (C' u)]
            _ = rowPermute ρ.symm (if f u then flipCol (C' u) else C' u) := by simp [hfu]
        · have hfu' : f u = false := by
            cases hx : f u
            · rfl
            · exfalso
              exact hfu hx
          have hh' := hh u
          rw [hfu'] at hh'
          simp at hh'
          calc
            C u = rowPermute ρ.symm (rowPermute ρ (C u)) := (rowPermute_left_inv ρ (C u)).symm
            _ = rowPermute ρ.symm (C' u) := by rw [← hh']
            _ = rowPermute ρ.symm (if f u then flipCol (C' u) else C' u) := by simp [hfu']
      simp [replaceColumn, hu, hmain]
  have hStrictC : UniversalStrictBetter (replaceColumn C t s₀) C := by
    intro ε hε0 hε1
    have h1 : lambda (replaceColumn C' t col5) ε > lambda C' ε := hStrict' ε hε0 hε1
    have h2 : lambda (replaceColumn C t s₀) ε = lambda (replaceColumn C' t col5) ε :=
      lambda_equiv (replaceColumn C' t col5) (replaceColumn C t s₀) hEqRep ε
    have h3 : lambda C' ε = lambda C ε :=
      lambda_equiv C C' ⟨ρ, Equiv.refl (Fin n), f, hh⟩ ε
    calc
      lambda (replaceColumn C t s₀) ε = lambda (replaceColumn C' t col5) ε := h2
      _ > lambda C' ε := h1
      _ = lambda C ε := h3
  have hs₀ : colVal s₀ = 3 ∨ colVal s₀ = 5 ∨ colVal s₀ = 6 ∨
      colVal s₀ = 9 ∨ colVal s₀ = 10 ∨ colVal s₀ = 12 := by
    rw [show s₀ = rowPermute ρ.symm col5 by simp [s₀, hft]]
    exact colVal_rowPermute_col5 ρ.symm
  exact strict_better_two_bit_col0 C t hcolC s₀ hs₀ hStrictC
end N4Code
