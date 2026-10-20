-- Prove2me | solution 1 for OAI.SingleFold.Counter.System.counter_info
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:32:22.730729+00:00
-- url     : https://prove2.me/submissions/9e5c10e4-4402-48bc-9651-cf29b952333b

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Theorems.Thm_OAI_SingleFold_Packed_bits_mask
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit

open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
variable (h : System M d v)
include h


theorem solution (j : Option J) : v.counter j < v.B^v.k ∧ ∀t < v.k,digit v.B (v.counter j) t < 2*v.b := by
  have hB2 : 2 ≤ v.B := by have := h.bound; unfold baseC at this; omega
  have hmask : v.mask = Packed.ones v.B v.k := by
    have hm := h.mask
    have hH := h.full
    rw [hH] at hm
    have hg : (v.B - 1) * Packed.ones v.B v.k = v.B ^ v.k - 1 := by
      unfold Packed.ones Packed.pack
      have hz : ((∑ t ∈ Finset.range v.k, (v.B:ℤ) ^ t) * ((v.B:ℤ) - 1)) = (v.B:ℤ) ^ v.k - 1 :=
        geom_sum_mul _ _
      have h1 : 1 ≤ v.B ^ v.k := Nat.one_le_pow _ _ (by omega)
      zify [h1, (by omega : 1 ≤ v.B)]
      push_cast
      simp only [one_mul]
      linarith
    have hpos : 0 < v.B - 1 := by omega
    exact Nat.eq_of_mul_eq_mul_left hpos (hm.trans hg.symm)
  have hc := (h.counter j).1
  rw [hmask, h.power] at hc
  have hw : 0 < v.w := by
    rcases Nat.eq_zero_or_pos v.w with h0 | h0
    · have := h.power; rw [h0] at this; omega
    · exact h0
  have hb : 2 * v.b - 1 < 2 ^ v.w := by
    have e1 := h.base; have e2 := h.power
    have : 2 ^ v.w = 4 * v.b := e2 ▸ e1
    omega
  have key := (Packed.bits_mask (x := v.counter j) (k := v.k) hw hb).1 hc
  rw [h.power]
  refine ⟨key.1, fun t ht => ?_⟩
  have h2 := key.2 t ht
  have h3 : Packed.digit (2 ^ v.w) (v.counter j) t ≤ 2 * v.b - 1 :=
    Nat.le_of_testBit ((Packed.bits_testBit _ _).1 h2)
  have hb1 : 1 ≤ v.b := by have := h.base; omega
  omega

